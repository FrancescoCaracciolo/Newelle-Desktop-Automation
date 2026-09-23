"""Newelle extension that searches and opens the applications installed on the user's computer.

Install it from Newelle: Settings -> Extensions -> "Install extension from file..." and pick this file.

Tools provided:
- search_program: find installed applications by name or keyword; results are also
  shown in the chat as a clickable list (clicking a row opens the application).
- open_program: launch an application, usually by the program ID returned by search_program.
"""

import os
import re
import shlex
import subprocess
import threading
import time
from gettext import gettext as _
from gettext import ngettext

from gi.repository import Gio, GLib, Gtk, Pango

from .extensions import NewelleExtension
from .tools import Tool, ToolResult
from .utility.system import can_escape_sandbox, get_spawn_command, is_flatpak

# Seconds before the cached application catalog is rebuilt
CATALOG_TTL = 30.0
DEFAULT_RESULTS = 8
MAX_RESULTS = 20
HOST_SCAN_TIMEOUT = 20
LAUNCH_TIMEOUT = 15

# Keys of a .desktop file that are needed to build a catalog entry
GREP_PATTERN = "^(Name|GenericName|Comment|Exec|Icon|NoDisplay|Hidden|Type|Terminal|Keywords)[=[]"

# Field codes in Exec= (see the desktop entry specification) are dropped on raw launch
FIELD_CODES = re.compile("%[a-zA-Z]")


def _language_names():
    try:
        return [lang for lang in GLib.get_language_names() if lang and lang != "C"]
    except Exception:
        return []


_LANGUAGES = _language_names()


def _localized(data, key):
    """Pick Name[locale]/Comment[locale] when it matches the user language, else the bare key."""
    for lang in _LANGUAGES:
        value = data.get(f"{key}[{lang}]")
        if value:
            return value
    return data.get(key, "")


def _parse_desktop_lines(lines):
    """Parse the [Desktop Entry] section of a .desktop file into a plain dict."""
    data = {}
    section = None
    for raw in lines:
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1]
            continue
        if section is not None and section != "Desktop Entry":
            continue
        key, sep, value = line.partition("=")
        if sep:
            data[key.strip()] = value.strip()
    return data


def _entry_from_data(data, path, desktop_id, local):
    """Build a catalog entry from parsed .desktop keys, or None if it must be skipped."""
    if data.get("Type", "Application") != "Application":
        return None
    if data.get("NoDisplay", "").lower() == "true" or data.get("Hidden", "").lower() == "true":
        return None
    name = _localized(data, "Name")
    command = data.get("Exec", "").strip()
    if not name or not command:
        return None
    return {
        "id": desktop_id,
        "name": name,
        "generic": _localized(data, "GenericName"),
        "comment": _localized(data, "Comment"),
        "exec": command,
        "icon": data.get("Icon", "").strip(),
        "keywords": [k.strip() for k in data.get("Keywords", "").split(";") if k.strip()],
        "terminal": data.get("Terminal", "").lower() == "true",
        "path": path,
        "local": local,
    }


def _exec_to_argv(exec_command):
    """Turn an Exec= value into an argument vector, dropping desktop field codes."""
    cleaned = FIELD_CODES.sub(" ", exec_command.replace("%%", "\x00")).replace("\x00", "%")
    try:
        return shlex.split(cleaned, posix=True)
    except ValueError:
        return cleaned.split()


def _match_score(entry, query, terms):
    name = entry["name"].lower()
    if name == query:
        return 100
    if name.startswith(query):
        return 80
    if query in name:
        return 60
    searchable = " ".join(
        (
            name,
            entry.get("generic") or "",
            entry.get("comment") or "",
            " ".join(entry.get("keywords") or []),
            entry.get("id", "").replace(".desktop", "").replace("-", " "),
            entry.get("exec") or "",
        )
    ).lower()
    if all(term in searchable for term in terms):
        return 25
    return 0


def _rank_catalog(catalog, query, limit):
    query = (query or "").strip().lower()
    if not query:
        return []
    terms = query.split()
    scored = []
    for entry in catalog.values():
        score = _match_score(entry, query, terms)
        if score:
            scored.append((score, entry))
    scored.sort(key=lambda pair: (-pair[0], pair[1]["name"].lower()))
    return [entry for _score, entry in scored[:limit]]


def _apply_icon(image, icon_name, pixel_size=32):
    """Set the best icon available for an application on a Gtk.Image, with a generic fallback."""
    image.set_pixel_size(pixel_size)
    name = (icon_name or "").strip()
    if name:
        if os.path.isabs(name):
            if os.path.isfile(name):
                try:
                    image.set_from_file(name)
                    return
                # Cosmetic fallback only: keep quiet when an icon cannot be loaded
                except (GLib.Error, OSError, ValueError):
                    pass
        else:
            try:
                display = Gtk.Display.get_default()
                if display is not None:
                    theme = Gtk.IconTheme.get_for_display(display)
                    if theme is not None and theme.has_icon(name):
                        image.set_from_icon_name(name)
                        return
            except (GLib.Error, OSError, ValueError):
                pass
    image.set_from_icon_name("application-x-executable-symbolic")


def get_app_icon(icon_name, pixel_size=32):
    image = Gtk.Image(valign=Gtk.Align.CENTER)
    _apply_icon(image, icon_name, pixel_size)
    return image


class AppResultsWidget(Gtk.Box):
    """Card shown in the chat listing the applications found by search_program."""

    def __init__(self, query, launcher=None):
        super().__init__(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        self.add_css_class("card")
        self.set_margin_top(8)
        self.set_margin_bottom(8)
        self.query = query
        # Blocking callable(entry) -> (success, message); when None the rows are not clickable
        self.launcher = launcher

        header = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=10)
        header.set_margin_top(8)
        header.set_margin_bottom(2)
        header.set_margin_start(10)
        header.set_margin_end(10)
        header_icon = Gtk.Image.new_from_icon_name("system-search-symbolic")
        header_icon.set_pixel_size(16)
        header.append(header_icon)
        self.title_label = Gtk.Label(
            xalign=0,
            hexpand=True,
            wrap=True,
            ellipsize=Pango.EllipsizeMode.END,
            css_classes=["heading"],
        )
        header.append(self.title_label)
        self.count_label = Gtk.Label(css_classes=["caption", "dim-label"])
        header.append(self.count_label)
        self.append(header)

        self.body = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
        self.body.set_margin_start(6)
        self.body.set_margin_end(6)
        self.body.set_margin_bottom(8)
        self.append(self.body)

        self._set_searching()

    def _clear_body(self):
        child = self.body.get_first_child()
        while child is not None:
            next_child = child.get_next_sibling()
            self.body.remove(child)
            child = next_child

    def _message_row(self, text, icon_name=None, spinning=False):
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=10)
        row.set_margin_top(8)
        row.set_margin_bottom(8)
        row.set_margin_start(10)
        row.set_margin_end(10)
        if spinning:
            spinner = Gtk.Spinner()
            spinner.start()
            row.append(spinner)
        elif icon_name is not None:
            icon = Gtk.Image.new_from_icon_name(icon_name)
            icon.set_pixel_size(16)
            row.append(icon)
        row.append(
            Gtk.Label(
                label=text,
                xalign=0,
                hexpand=True,
                wrap=True,
                css_classes=["dim-label"],
            )
        )
        return row

    def _set_searching(self):
        self._clear_body()
        self.title_label.set_text(_('Searching applications'))
        self.count_label.set_text("")
        self.body.append(
            self._message_row(
                _('Looking for "{0}" on this computer...').format(self.query),
                spinning=True,
            )
        )

    def set_results(self, matches):
        self._clear_body()
        count = len(matches)
        self.title_label.set_text(_('Applications matching "{0}"').format(self.query))
        self.count_label.set_text(ngettext("{0} application", "{0} applications", count).format(count))
        if not count:
            self.body.append(self._message_row(_("No applications found"), "system-search-symbolic"))
            return
        list_box = Gtk.ListBox(
            selection_mode=Gtk.SelectionMode.NONE,
            css_classes=["boxed-list"],
        )
        if self.launcher is not None:
            list_box.connect("row-activated", self._on_row_activated)
        for entry in matches:
            list_box.append(self._create_row(entry))
        self.body.append(list_box)

    def set_error(self, message):
        self._clear_body()
        self.title_label.set_text(_("Search failed"))
        self.count_label.set_text("")
        self.body.append(self._message_row(message, "dialog-warning-symbolic"))

    def set_stale(self):
        self._clear_body()
        self.title_label.set_text(_('Applications matching "{0}"').format(self.query))
        self.count_label.set_text("")
        self.body.append(
            self._message_row(
                _("These search results are no longer available. Search again to refresh them."),
                "dialog-information-symbolic",
            )
        )

    def _create_row(self, entry):
        row = Gtk.ListBoxRow(
            activatable=self.launcher is not None,
            selectable=False,
            tooltip_text=entry["id"],
        )
        row.entry = entry
        row.launching = False
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=12)
        box.set_margin_top(8)
        box.set_margin_bottom(8)
        box.set_margin_start(8)
        box.set_margin_end(8)
        icon = get_app_icon(entry.get("icon"))
        row.icon_image = icon
        box.append(icon)
        labels = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2, hexpand=True)
        labels.append(
            Gtk.Label(
                label=entry["name"],
                xalign=0,
                hexpand=True,
                wrap=True,
                css_classes=["heading"],
            )
        )
        subtitle = entry.get("comment") or entry.get("generic") or entry.get("id")
        if subtitle:
            labels.append(
                Gtk.Label(
                    label=subtitle,
                    xalign=0,
                    hexpand=True,
                    wrap=True,
                    ellipsize=Pango.EllipsizeMode.END,
                    css_classes=["caption", "dim-label"],
                )
            )
        box.append(labels)
        if entry.get("terminal"):
            badge = Gtk.Image.new_from_icon_name("utilities-terminal-symbolic")
            badge.set_pixel_size(14)
            badge.set_valign(Gtk.Align.CENTER)
            badge.add_css_class("dim-label")
            box.append(badge)
        row.set_child(box)
        return row

    def _on_row_activated(self, list_box, row):
        if self.launcher is None or row.launching:
            return
        row.launching = True
        row.set_sensitive(False)
        row.icon_image.set_from_icon_name("content-loading-symbolic")
        entry = row.entry

        def work():
            success, _message = self.launcher(entry)

            def finished():
                row.icon_image.set_from_icon_name(
                    "object-select-symbolic" if success else "dialog-warning-symbolic"
                )

            GLib.idle_add(finished)

        threading.Thread(target=work, daemon=True).start()


class AppLaunchWidget(Gtk.Box):
    """Status card shown in the chat by the open_program tool."""

    def __init__(self, program):
        super().__init__(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        self.add_css_class("card")
        self.set_margin_top(8)
        self.set_margin_bottom(8)
        self.program = program
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=12)
        box.set_margin_top(10)
        box.set_margin_bottom(10)
        box.set_margin_start(10)
        box.set_margin_end(10)
        self.icon_image = Gtk.Image(valign=Gtk.Align.CENTER)
        _apply_icon(self.icon_image, None)
        box.append(self.icon_image)
        labels = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2, hexpand=True)
        self.title_label = Gtk.Label(
            xalign=0, hexpand=True, wrap=True, ellipsize=Pango.EllipsizeMode.END, css_classes=["heading"]
        )
        self.status_label = Gtk.Label(
            xalign=0,
            hexpand=True,
            wrap=True,
            ellipsize=Pango.EllipsizeMode.END,
            css_classes=["caption", "dim-label"],
        )
        labels.append(self.title_label)
        labels.append(self.status_label)
        box.append(labels)
        self.spinner = Gtk.Spinner(valign=Gtk.Align.CENTER)
        box.append(self.spinner)
        self.append(box)
        self.set_state(None, _("Opening {0}").format(program), _("Looking for the application..."), spinning=True)

    def set_state(self, icon_name, title, status, spinning=False):
        if icon_name is not None:
            self.icon_image.set_from_icon_name(icon_name)
        self.title_label.set_text(title)
        self.status_label.set_text(status)
        if spinning:
            self.spinner.start()
        else:
            self.spinner.stop()
        self.spinner.set_visible(spinning)

    def set_launching(self, entry):
        _apply_icon(self.icon_image, entry.get("icon"))
        self.set_state(None, entry["name"], _("Opening..."), spinning=True)

    def set_result(self, success, entry, message=None):
        _apply_icon(self.icon_image, entry.get("icon"))
        if success:
            self.set_state(None, entry["name"], _("Opened") + (message or ""))
        else:
            self.set_state("dialog-warning-symbolic", entry["name"], _("Could not open the application"))
            if message:
                self.status_label.set_text(message)

    def set_not_found(self, program):
        self.set_state(
            "dialog-warning-symbolic",
            _("Application not found"),
            _('"{0}" is not installed or is not visible to Newelle').format(program),
        )

    def set_stale(self, entry=None):
        if entry is not None:
            _apply_icon(self.icon_image, entry.get("icon"))
            self.set_state(None, entry["name"], _("Opened from a previous conversation"))
        else:
            self.set_state(None, self.program, _("Opened from a previous conversation"))


class AppLauncherExtension(NewelleExtension):
    name = "App Launcher"
    id = "applauncher"

    def __init__(self, pip_path, extension_path, settings, **kwargs):
        super().__init__(pip_path, extension_path, settings)
        self._catalog = None
        self._catalog_time = 0.0
        self._catalog_lock = threading.Lock()
        self._can_spawn_cache = None

    @staticmethod
    def requires_sandbox_escape():
        # Host applications live outside the Flatpak sandbox and need flatpak-spawn
        return True

    # Catalog building

    def _data_home(self):
        return os.environ.get("XDG_DATA_HOME") or os.path.join(os.path.expanduser("~"), ".local", "share")

    def _application_dirs(self):
        dirs = [os.path.join(self._data_home(), "applications")]
        for data_dir in (os.environ.get("XDG_DATA_DIRS") or "/usr/local/share:/usr/share").split(":"):
            data_dir = data_dir.strip()
            if data_dir:
                dirs.append(os.path.join(data_dir, "applications"))
        dirs.append("/var/lib/flatpak/exports/share/applications")
        dirs.append(os.path.join(self._data_home(), "flatpak", "exports", "share", "applications"))
        unique = []
        for directory in dirs:
            if directory not in unique:
                unique.append(directory)
        return unique

    def _local_scan_dirs(self):
        dirs = self._application_dirs()
        if is_flatpak():
            # Inside the sandbox /usr belongs to the runtime, not to the host:
            # those applications are picked up by the host scan instead.
            dirs = [d for d in dirs if not d.startswith("/usr")]
        return [d for d in dirs if os.path.isdir(d)]

    def _host_scan_dirs(self):
        # The sandbox XDG_DATA_DIRS does not describe the host, so probe the
        # standard locations explicitly.
        return [
            os.path.join(self._data_home(), "applications"),
            "/usr/local/share/applications",
            "/usr/share/applications",
            "/var/lib/flatpak/exports/share/applications",
            os.path.join(self._data_home(), "flatpak", "exports", "share", "applications"),
        ]

    def _can_spawn(self):
        if self._can_spawn_cache is None:
            self._can_spawn_cache = can_escape_sandbox()
        return self._can_spawn_cache

    def _scan_local(self):
        entries = {}
        for app_dir in self._local_scan_dirs():
            for root, _subdirs, files in os.walk(app_dir):
                for file_name in files:
                    if not file_name.endswith(".desktop"):
                        continue
                    path = os.path.join(root, file_name)
                    try:
                        with open(path, encoding="utf-8", errors="replace") as handle:
                            data = _parse_desktop_lines(handle)
                    except OSError:
                        continue
                    desktop_id = self._desktop_id(app_dir, path)
                    entry = _entry_from_data(data, path, desktop_id, local=True)
                    if entry is not None:
                        entries.setdefault(desktop_id, entry)
        return entries

    def _scan_host(self):
        """Fetch .desktop data for host applications with a single flatpak-spawn call."""
        entries = {}
        app_dirs = self._host_scan_dirs()
        try:
            proc = subprocess.run(
                get_spawn_command() + ["grep", "-rsHE", GREP_PATTERN] + app_dirs,
                capture_output=True,
                text=True,
                timeout=HOST_SCAN_TIMEOUT,
                check=False,
            )
        except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
            return entries
        raw = {}
        for line in proc.stdout.splitlines():
            path, sep, key_value = line.partition(":")
            if not sep:
                continue
            key, key_sep, value = key_value.partition("=")
            if key_sep:
                raw.setdefault(path, {})[key.strip()] = value.strip()
        for path, data in raw.items():
            app_dir = next((d for d in app_dirs if path.startswith(d + os.sep)), None)
            if app_dir is None:
                continue
            desktop_id = self._desktop_id(app_dir, path)
            entry = _entry_from_data(data, path, desktop_id, local=False)
            if entry is not None:
                entries.setdefault(desktop_id, entry)
        return entries

    @staticmethod
    def _desktop_id(app_dir, path):
        relative = os.path.relpath(path, app_dir)
        return relative.replace(os.sep, "-")

    def _get_catalog(self):
        with self._catalog_lock:
            now = time.time()
            if self._catalog is None or now - self._catalog_time > CATALOG_TTL:
                catalog = self._scan_local()
                if is_flatpak() and self._can_spawn():
                    for desktop_id, entry in self._scan_host().items():
                        catalog.setdefault(desktop_id, entry)
                self._catalog = catalog
                self._catalog_time = now
            return self._catalog

    # Searching and launching

    def _search(self, query, limit):
        return _rank_catalog(self._get_catalog(), query, limit)

    @staticmethod
    def _normalize_limit(limit):
        try:
            return max(1, min(int(limit or DEFAULT_RESULTS), MAX_RESULTS))
        except (TypeError, ValueError):
            return DEFAULT_RESULTS

    def _lookup(self, catalog, program):
        program = (program or "").strip()
        if not program:
            return None
        candidates = [program]
        if not program.endswith(".desktop"):
            candidates.append(program + ".desktop")
        for key in candidates:
            if key in catalog:
                return catalog[key]
        lowered = program.lower()
        exact = [entry for entry in catalog.values() if entry["name"].lower() == lowered]
        if len(exact) == 1:
            return exact[0]
        ranked = _rank_catalog(catalog, lowered, 1)
        return ranked[0] if ranked else None

    def _launch(self, entry):
        """Launch an application entry. Returns (success, message)."""
        if os.path.isfile(entry["path"]):
            # Preferred path: GLib resolves field codes, terminal wrappers and,
            # inside a sandbox, launches through the Flatpak portal.
            try:
                app_info = Gio.DesktopAppInfo.new_from_filename(entry["path"])
            except Exception as error:
                print(f"App launcher: DesktopAppInfo error: {error}")
                app_info = None
            if app_info is not None:
                try:
                    if app_info.launch(None, None):
                        return True, ""
                except Exception as error:
                    print(f"App launcher: DesktopAppInfo launch error: {error}")
            gio_error = ""
        if self._can_spawn():
            try:
                proc = subprocess.run(
                    get_spawn_command() + ["gio", "launch", entry["path"]],
                    capture_output=True,
                    text=True,
                    timeout=LAUNCH_TIMEOUT,
                    check=False,
                )
                if proc.returncode == 0:
                    return True, ""
                gio_error = (proc.stderr or proc.stdout or "").strip()
            except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as error:
                gio_error = str(error)
            argv = _exec_to_argv(entry["exec"])
            if argv:
                try:
                    subprocess.Popen(
                        get_spawn_command() + argv,
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                        start_new_session=True,
                    )
                    note = ""
                    if entry["terminal"]:
                        note = _(" (launched directly, so it may not work because it needs a terminal)")
                    return True, note
                except (FileNotFoundError, OSError) as error:
                    return False, f"gio launch: {gio_error}; {error}"
            return False, gio_error or "gio launch failed"
        return False, _("Newelle is sandboxed and cannot run commands on the host system")

    def _sandbox_hint(self):
        if not is_flatpak() or self._can_spawn():
            return ""
        return (
            " "
            + _("Ask the user to run: flatpak --user override --talk-name=org.freedesktop.Flatpak io.github.qwersyk.Newelle")
        )

    # Tools

    def _tool_search(self, query: str, limit: int = DEFAULT_RESULTS, tool_uuid=None, chat_id=None) -> ToolResult:
        result = ToolResult()
        widget = AppResultsWidget(query, launcher=self._launch)
        result.set_widget(widget)
        limit = self._normalize_limit(limit)

        def work():
            try:
                if not (query or "").strip():
                    GLib.idle_add(widget.set_error, _("The search query is empty"))
                    result.set_output("The search query is empty. Ask the user which application they want to open.")
                    return
                matches = self._search(query, limit)
                GLib.idle_add(lambda: widget.set_results(matches))
                result.set_output(self._format_search_output(query, matches))
                result.set_display_text(
                    ngettext(
                        'Found {0} application matching "{1}"',
                        'Found {0} applications matching "{1}"',
                        len(matches),
                    ).format(len(matches), query)
                )
            except Exception as error:
                # Bind eagerly: the except variable is deleted when the block ends
                GLib.idle_add(widget.set_error, f"{error}")
                result.set_output(f"Error while searching for programs: {error}")

        threading.Thread(target=work, daemon=True).start()
        return result

    def _format_search_output(self, query, matches):
        if not matches:
            return (
                f'No installed applications found matching "{query}". '
                "Tell the user, and suggest checking the spelling or trying a shorter name."
                + self._sandbox_hint()
            )
        lines = [f'Found {len(matches)} installed applications matching "{query}":', ""]
        for index, entry in enumerate(matches, 1):
            lines.append(f"{index}. {entry['name']}")
            lines.append(f"   ID: {entry['id']}")
            if entry["comment"]:
                lines.append(f"   Description: {entry['comment']}")
            if entry["terminal"]:
                lines.append("   Note: this application runs in a terminal.")
        lines.append("")
        lines.append(
            "To open one of them, call open_program with the exact 'program' ID listed above "
            f"(for example: {matches[0]['id']})."
        )
        return "\n".join(lines) + self._sandbox_hint()

    def _tool_open(self, program: str, tool_uuid=None, chat_id=None) -> ToolResult:
        result = ToolResult()
        widget = AppLaunchWidget(program)
        result.set_widget(widget)

        def work():
            try:
                entry = self._lookup(self._get_catalog(), program)
                if entry is None:
                    GLib.idle_add(lambda: widget.set_not_found(program))
                    result.set_output(
                        f'No installed application found for "{program}". '
                        "Call search_program to find the correct program ID, then call open_program again."
                        + self._sandbox_hint()
                    )
                    result.set_display_text(f'"{program}" was not found')
                    return
                GLib.idle_add(lambda: widget.set_launching(entry))
                success, message = self._launch(entry)
                GLib.idle_add(lambda: widget.set_result(success, entry, message))
                if success:
                    output = f"Successfully opened {entry['name']} ({entry['id']})." + (message or "")
                    result.set_output(output)
                    result.set_display_text(f"Opened {entry['name']}")
                else:
                    result.set_output(
                        f"Failed to open {entry['name']} ({entry['id']}): {message}" + self._sandbox_hint()
                    )
                    result.set_display_text(f"Could not open {entry['name']}")
            except Exception as error:
                result.set_output(f"Error while opening the program: {error}")

        threading.Thread(target=work, daemon=True).start()
        return result

    # Chat reload: rebuild the widgets without running the tools again

    def _restore_search(self, query: str, limit: int = DEFAULT_RESULTS, tool_uuid=None, chat_id=None) -> ToolResult:
        result = ToolResult()
        result.set_output(None)
        widget = AppResultsWidget(query, launcher=self._launch)
        try:
            if self._catalog is not None:
                matches = _rank_catalog(self._catalog, query, self._normalize_limit(limit))
                widget.set_results(matches)
            else:
                widget.set_stale()
        except Exception:
            widget.set_stale()
        result.set_widget(widget)
        return result

    def _restore_open(self, program: str, tool_uuid=None, chat_id=None) -> ToolResult:
        result = ToolResult()
        result.set_output(None)
        widget = AppLaunchWidget(program)
        try:
            entry = self._lookup(self._get_catalog(), program) if self._catalog is not None else None
            saved_output = None
            if tool_uuid and getattr(self, "ui_controller", None) is not None:
                try:
                    saved_output = self.ui_controller.get_tool_result_by_id(tool_uuid)
                except Exception:
                    saved_output = None
            success = bool(saved_output) and saved_output.startswith("Successfully opened")
            if entry is not None and success:
                widget.set_result(True, entry)
            elif entry is not None:
                widget.set_stale(entry)
            else:
                widget.set_stale()
        except Exception:
            widget.set_stale()
        result.set_widget(widget)
        return result

    def get_tools(self) -> list:
        return [
            Tool(
                name="search_program",
                description=(
                    "Search for applications installed on the user's computer by name or keyword. "
                    "Returns the matching applications with their unique program ID. "
                    "When the user asks to open an app, call this tool first, then call open_program "
                    "with one of the returned IDs."
                ),
                func=self._tool_search,
                title=_("Search Programs"),
                schema={
                    "type": "object",
                    "properties": {
                        "query": {
                            "type": "string",
                            "description": "Name or keyword to search for, e.g. 'firefox', 'calculator', 'text editor'",
                        },
                        "limit": {
                            "type": "integer",
                            "description": "Maximum number of results to return (default 8)",
                        },
                    },
                    "required": ["query"],
                },
                restore_func=self._restore_search,
                tools_group=_("System"),
                icon_name="system-search-symbolic",
            ),
            Tool(
                name="open_program",
                description=(
                    "Open an application installed on the user's computer. "
                    "Pass the exact program ID returned by search_program "
                    "(for example 'org.gnome.Calculator.desktop'); "
                    "the application name is also accepted when it is already known."
                ),
                func=self._tool_open,
                title=_("Open Program"),
                schema={
                    "type": "object",
                    "properties": {
                        "program": {
                            "type": "string",
                            "description": "Program ID from search_program (preferred) or exact application name",
                        },
                    },
                    "required": ["program"],
                },
                restore_func=self._restore_open,
                tools_group=_("System"),
                icon_name="application-x-executable-symbolic",
            ),
        ]
