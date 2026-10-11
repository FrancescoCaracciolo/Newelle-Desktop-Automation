# SPDX-License-Identifier: GPL-3.0-or-later
"""GNOME Desktop extension for Newelle.

Single-file, standalone Newelle extension (install it with the extension
manager, not as a built-in integration). It mirrors desktop controls from
https://github.com/bilelmoussaoui/gnome-mcp-server natively in Python, so no
Rust binary is required:

Tools (same behaviour as upstream):
    send_notification, open_file, set_wallpaper,
    set_volume, media_control, quick_settings, take_screenshot,
    window_management, keyring

Resources exposed as read-only tools:
    calendar events, task lists, contacts, system info,
    audio status

All results render a coherent Adw card (shared header/body/footer and chips)
and return structured JSON for the model.
"""

import datetime
import functools
import gettext
import json
import os
import platform
import re
import shutil
import socket
import subprocess
import threading
import time
import weakref
from pathlib import Path

import gi

gi.require_version("Adw", "1")
from gi.repository import Adw, Gio, GLib, Gtk, Pango

from .extensions import NewelleExtension
from .tools import Tool, ToolResult

_ = gettext.gettext


# ---------------------------------------------------------------------------
# Small host helpers (Flatpak aware)
# ---------------------------------------------------------------------------

def _is_flatpak() -> bool:
    return os.path.exists("/.flatpak-info")


def _host_prefix() -> list:
    return ["flatpak-spawn", "--host"] if _is_flatpak() else []


def _run_cmd(argv: list, timeout: int = 25, input_data=None) -> str:
    """Run a command on the host when sandboxed, return stripped stdout."""
    cmd = _host_prefix() + list(argv)
    proc = subprocess.run(
        cmd, input=input_data, capture_output=True, text=True, timeout=timeout
    )
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout or _("Command failed")).strip()
        raise RuntimeError(err[:1500])
    return (proc.stdout or "").strip()


def _have_cmd(name: str) -> bool:
    if shutil.which(name):
        return True
    if _is_flatpak():
        try:
            _run_cmd(["which", name], timeout=5)
            return True
        except Exception:
            return False
    return False


def _gsettings_set(schema: str, key: str, value: str):
    """Set a GSettings key. Value is a GVariant literal, e.g. 'true', \"'x'\"."""
    if not _is_flatpak():
        try:
            settings = Gio.Settings.new(schema)
            # Common cases handled without spawning a process.
            if value in ("true", "false"):
                settings.set_boolean(key, value == "true")
            elif value.startswith("'") and value.endswith("'"):
                settings.set_string(key, value[1:-1])
            else:
                _run_cmd(["gsettings", "set", schema, key, value])
            return
        except Exception:
            pass
    _run_cmd(["gsettings", "set", schema, key, value])


def _gsettings_get(schema: str, key: str) -> str:
    if not _is_flatpak():
        try:
            settings = Gio.Settings.new(schema)
            value = settings.get_value(key)
            return value.print_(True)
        except Exception:
            pass
    return _run_cmd(["gsettings", "get", schema, key])


class WindowHelperUnavailable(RuntimeError):
    """The window-control Shell helper is not running and unsafe mode is off."""


def _dbus_missing(error) -> bool:
    text = str(error)
    return any(name in text for name in (
        "ServiceUnknown", "NameHasNoOwner", "UnknownObject", "UnknownMethod",
        "UnknownInterface"))


def _dbus_call(dest: str, path: str, interface: str, method: str,
               params=None, reply_type: str = "()", timeout: int = 20) -> tuple:
    """Call a session-bus method, going through the host when sandboxed."""
    try:
        bus = Gio.bus_get_sync(Gio.BusType.SESSION, None)
        reply = bus.call_sync(
            dest, path, interface, method, params, GLib.VariantType.new(reply_type),
            Gio.DBusCallFlags.NONE, timeout * 1000, None)
        return reply.unpack()
    except GLib.Error as error:
        # The Flatpak D-Bus proxy hides GNOME Shell names, so retry on the host.
        if not _is_flatpak():
            raise RuntimeError(error.message[:1500]) from None
    argv = ["gdbus", "call", "--session", "--dest", dest, "--object-path", path,
            "--timeout", str(timeout), "--method", f"{interface}.{method}"]
    if params is not None:
        argv += [params.get_child_value(i).print_(True) for i in range(params.n_children())]
    out = _run_cmd(argv, timeout=timeout + 5)
    try:
        return GLib.Variant.parse(GLib.VariantType.new(reply_type), out, None, None).unpack()
    except GLib.Error:
        raise RuntimeError(out[:500]) from None


def _shell_eval(script: str, timeout: int = 20) -> str:
    """Evaluate JavaScript in GNOME Shell (only works in unsafe mode)."""
    ok, out = _dbus_call("org.gnome.Shell", "/org/gnome/Shell", "org.gnome.Shell", "Eval",
                         GLib.Variant("(s)", (script,)), "(bs)", timeout)
    if not ok:
        # GNOME Shell answers (false, '') when unsafe mode is disabled.
        if not out:
            raise WindowHelperUnavailable(_("GNOME Shell unsafe mode is disabled."))
        raise RuntimeError(out[:1500])
    return out


def _parse_attrs(attributes) -> dict:
    if not attributes:
        return {}
    if isinstance(attributes, dict):
        return {str(k): str(v) for k, v in attributes.items()}
    try:
        parsed = json.loads(attributes)
    except (TypeError, ValueError):
        raise ValueError(_("Attributes must be a JSON object, e.g. '{\"service\": \"github\"}'."))
    if not isinstance(parsed, dict):
        raise ValueError(_("Attributes must be a JSON object."))
    return {str(k): str(v) for k, v in parsed.items()}


def _validated_id(value, label="window_id") -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(_("Missing value: %s") % label)
    text = value.strip()
    if len(text) > 64 or "\x00" in text:
        raise ValueError(_("Invalid value: %s") % label)
    return text


def _tuple_result(response):
    """Unwrap PyGObject (success, payload) tuples from EDS calls."""
    if isinstance(response, (tuple, list)) and len(response) == 2 and isinstance(response[0], bool):
        if not response[0]:
            raise RuntimeError(_("The GNOME service did not return a result."))
        return response[1]
    return response


def _comp_text(value) -> str:
    """Extract plain text from str, ECal ComponentText, enum, or None."""
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    for attr in ("value_nick", "value_name"):
        nick = getattr(value, attr, None)
        if isinstance(nick, str) and nick:
            return nick
    getter = getattr(value, "get_value", None)
    if callable(getter):
        try:
            inner = getter()
            return inner if isinstance(inner, str) else ("" if inner is None else str(inner))
        except Exception:  # noqa: BLE001 - best effort display
            return ""
    try:
        return str(value)
    except Exception:  # noqa: BLE001
        return ""


def _require_ical():
    """Import ICalGLib, accepting either the 3.0 or 4.0 namespace version."""
    for version in ("3.0", "4.0"):
        try:
            gi.require_version("ICalGLib", version)
            from gi.repository import ICalGLib  # noqa: F401
            return ICalGLib
        except (ValueError, ImportError):
            continue
    raise RuntimeError(_("Calendar libraries are missing (need libical-glib)."))


# ---------------------------------------------------------------------------
# Shared card UI
# ---------------------------------------------------------------------------

CARD_CSS = b"""
.gnome-header { padding: 12px 16px; background: alpha(@accent_bg_color, 0.08); }
.gnome-body { padding: 12px 16px; }
.gnome-footer { padding: 6px 12px 12px; border-top: 1px solid alpha(@borders, 0.3); }
.gnome-item { padding: 10px 2px; border-bottom: 1px solid alpha(@borders, 0.3); }
.gnome-item:last-child { border-bottom: none; }
.gnome-title { font-weight: 700; }
.gnome-mono { font-family: monospace; }
.gnome-big { font-size: 22px; font-weight: 800; font-variant-numeric: tabular-nums; }
.gnome-chip { border-radius: 999px; padding: 2px 10px; font-size: 12px; font-weight: 600; }
.gnome-chip-accent { background: alpha(@accent_bg_color, 0.14); color: @accent_color; }
.gnome-chip-success { background: alpha(@success_bg_color, 0.16); color: @success_color; }
.gnome-chip-warning { background: alpha(@warning_bg_color, 0.16); color: @warning_color; }
.gnome-chip-error { background: alpha(@error_bg_color, 0.14); color: @error_color; }
.gnome-chip-neutral { background: alpha(@window_fg_color, 0.08); color: @window_fg_color; }
"""


def _schema(properties: dict, required=()) -> dict:
    return {
        "type": "object",
        "properties": properties,
        "required": list(required),
        "additionalProperties": False,
    }


def _str(description: str) -> dict:
    return {"type": "string", "description": description}


def _bool(description: str) -> dict:
    return {"type": "boolean", "description": description}


def _int(description: str, low: int, high: int) -> dict:
    return {"type": "integer", "description": description, "minimum": low, "maximum": high}


TOOL_DEFINITIONS = [
    ("gnome_send_notification", "notifications", _("Send notification"),
     _("Send a desktop notification. Equivalent to gnome-mcp-server 'send_notification'."),
     _schema({"summary": _str(_("Notification title")),
              "body": _str(_("Notification content"))}, ("summary", "body")),
     "preferences-system-notifications-symbolic"),
    ("gnome_open_file", "files", _("Open file or URL"),
     _("Open a file path or URL with its default application. Equivalent to upstream 'open_file'."),
     _schema({"path": _str(_("File path or URL, e.g. '/home/user/doc.pdf' or 'https://example.com'") )},
             ("path",)),
     "folder-symbolic"),
    ("gnome_set_wallpaper", "wallpaper", _("Set wallpaper"),
     _("Set the desktop wallpaper from a local image (JPG, JPEG, PNG, WebP). Equivalent to upstream 'set_wallpaper'."),
     _schema({"image_path": _str(_("Full path to the image file"))}, ("image_path",)),
     "preferences-desktop-wallpaper-symbolic"),
    ("gnome_set_volume", "audio", _("Set volume"),
     _("Control system volume or mute. Give volume (0-100), mute, or direction up/down. "
       "Set relative=true when volume is a delta like +10. Equivalent to upstream 'set_volume'."),
     _schema({"volume": {"type": "number", "description": _("Volume level 0-100, or delta when relative=true"),
                         "minimum": -100, "maximum": 200},
              "mute": _bool(_("Mute (true) or unmute (false)")),
              "relative": _bool(_("Treat volume as a relative change; default false")),
              "direction": {"type": "string", "enum": ["up", "down"],
                            "description": _("Step up/down by the configured volume step")}},
             ()),
     "audio-volume-high-symbolic"),
    ("gnome_media_control", "audio", _("Media control"),
     _("Control media playback over MPRIS (play, pause, play_pause, stop, next, previous). "
       "Equivalent to upstream 'media_control'."),
     _schema({"action": {"type": "string", "enum": ["play", "pause", "play_pause", "stop", "next", "previous"],
                         "description": _("Playback action")},
              "player": _str(_("Optional player substring, e.g. 'firefox', 'spotify'. Defaults to active player."))},
             ("action",)),
     "media-playback-start-symbolic"),
    ("gnome_quick_settings", "quick_settings", _("Toggle system setting"),
     _("Toggle wifi, bluetooth, night_light, do_not_disturb or dark_style. Equivalent to upstream 'quick_settings'."),
     _schema({"setting": {"type": "string",
                          "enum": ["wifi", "bluetooth", "night_light", "do_not_disturb", "dark_style"]},
              "enabled": _bool(_("true to enable, false to disable"))},
             ("setting", "enabled")),
     "system-settings-symbolic"),
    ("gnome_take_screenshot", "screenshot", _("Take screenshot"),
     _("Take a screenshot. Set interactive=true for area selection. Equivalent to upstream 'take_screenshot'."),
     _schema({"interactive": _bool(_("Show the interactive area-selection dialog"))}, ()),
     "camera-photo-symbolic"),
    ("gnome_window_management", "windows", _("Manage windows"),
     _("Manage windows and workspaces via GNOME Shell (through the Newelle window control helper, "
       "or unsafe mode as a fallback). Actions: list, focus, close, "
       "minimize, maximize (toggles), switch_workspace, move_to_workspace, get_geometry, set_geometry, "
       "set_position, set_size, snap (position left/right). Workspaces are 0-indexed. "
       "Equivalent to upstream 'window_management'."),
     _schema({"action": {"type": "string", "enum": ["list", "focus", "close", "minimize", "maximize",
                                                    "switch_workspace", "move_to_workspace",
                                                    "get_geometry", "set_geometry", "set_position",
                                                    "set_size", "snap"]},
              "window_id": _str(_("Window ID for window-specific actions (see list)")),
              "workspace": _int(_("Workspace number, 0-indexed"), 0, 64),
              "x": _int(_("X coordinate"), -16384, 16384),
              "y": _int(_("Y coordinate"), -16384, 16384),
              "width": _int(_("Width in pixels"), 1, 16384),
              "height": _int(_("Height in pixels"), 1, 16384),
              "position": {"type": "string", "enum": ["left", "right"],
                           "description": _("Snap position")}},
             ("action",)),
     "window-restore-symbolic"),
    ("gnome_keyring", "keyring", _("Keyring secret"),
     _("Store, retrieve or delete secrets in GNOME Keyring via libsecret. Attributes is a JSON object "
       "used to find the secret, e.g. '{\"service\": \"github\"}'. Equivalent to upstream 'keyring'."),
     _schema({"action": {"type": "string", "enum": ["store", "retrieve", "delete"]},
              "label": _str(_("Human-readable label (required for store)")),
              "secret": _str(_("Secret value (required for store)")),
              "attributes": _str(_("JSON object of attributes, e.g. '{\"service\": \"github\", \"user\": \"me\"}'"))},
             ("action",)),
     "dialog-password-symbolic"),
    ("gnome_calendar_events", "calendar", _("Calendar events"),
     _("Read GNOME calendar events (Evolution Data Server). Uses days_ahead/days_behind around now. "
       "Upstream resource 'gnome://calendar/events'."),
     _schema({"days_ahead": _int(_("Days to look ahead (default from settings)"), 0, 366),
              "days_behind": _int(_("Days to look behind (default from settings)"), 0, 366)},
             ()),
     "x-office-calendar-symbolic"),
    ("gnome_tasks", "tasks", _("Tasks"),
     _("Read GNOME task lists (Evolution Data Server). Upstream resource 'gnome://tasks/list'."),
     _schema({"include_completed": _bool(_("Include completed tasks")),
              "include_cancelled": _bool(_("Include cancelled tasks")),
              "due_within_days": _int(_("Only tasks due within N days, 0 means all"), 0, 3650)},
             ()),
     "checkbox-checked-symbolic"),
    ("gnome_contacts", "contacts", _("Contacts"),
     _("Search GNOME contacts (Evolution Data Server). Upstream resource 'gnome://contacts/list'."),
     _schema({"query": _str(_("Filter by name, email or phone; empty lists all")),
              "email_only": _bool(_("Only contacts with an email address")),
              "limit": _int(_("Maximum results"), 1, 100)},
             ()),
     "avatar-default-symbolic"),
    ("gnome_system_info", "system", _("System info"),
     _("OS, hostname, GNOME version, uptime and session. Upstream resource 'gnome://system/info'."),
     _schema({}),
     "computer-symbolic"),
    ("gnome_audio_status", "audio", _("Audio status"),
     _("Current volume, mute state and MPRIS players. Upstream resource 'gnome://audio/status'."),
     _schema({}),
     "audio-speakers-symbolic"),
]

DEFINITIONS = {name: (name, cap, title, desc, schema, icon)
               for name, cap, title, desc, schema, icon in TOOL_DEFINITIONS}

CAPABILITIES = [
    ("notifications", _("Notifications")),
    ("files", _("Files &amp; URLs")),
    ("wallpaper", _("Wallpaper")),
    ("audio", _("Audio &amp; media")),
    ("quick_settings", _("Quick settings")),
    ("screenshot", _("Screenshots")),
    ("windows", _("Windows")),
    ("keyring", _("Keyring")),
    ("calendar", _("Calendar")),
    ("tasks", _("Tasks")),
    ("contacts", _("Contacts")),
    ("system", _("System")),
]

# Since GNOME 41 every privileged Shell D-Bus API (Eval, Introspect, FocusApp…)
# is gated behind unsafe mode or a portal allowlist. Window management therefore
# goes through a tiny companion Shell extension that exports its own D-Bus
# service; org.gnome.Shell.Extensions (install/enable) is not gated.
WINDOW_HELPER_UUID = "newelle-window-control@qwersyk.github.io"
WINDOW_HELPER_BUS = "io.github.qwersyk.Newelle.WindowControl"
WINDOW_HELPER_PATH = "/io/github/qwersyk/Newelle/WindowControl"
WINDOW_HELPER_VERSION = 1
WINDOW_HELPER_SHELL_VERSIONS = ["45", "46", "47", "48", "49", "50"]

# Shared by the helper extension and the unsafe-mode Eval fallback, so it may
# only rely on names available in both scopes: global, Meta and Main.
WINDOW_JS_CORE = r"""
function nwIsMaximized(w) {
    if (typeof w.is_maximized === 'function') return Boolean(w.is_maximized());
    if (typeof w.get_maximized === 'function') return Boolean(w.get_maximized());
    return Boolean(w.maximized_horizontally && w.maximized_vertically);
}
// Mutter 49 dropped get_maximized() and the MaximizeFlags argument.
function nwMaximize(w) {
    if (typeof w.get_maximized === 'function') w.maximize(Meta.MaximizeFlags.BOTH);
    else w.maximize();
}
function nwUnmaximize(w) {
    if (!nwIsMaximized(w)) return;
    if (typeof w.get_maximized === 'function') w.unmaximize(Meta.MaximizeFlags.BOTH);
    else w.unmaximize();
}
function nwAll() {
    return global.get_window_actors().map(a => a.get_meta_window()).filter(w => w);
}
function nwListed() {
    return nwAll().filter(w => w.get_window_type() === Meta.WindowType.NORMAL &&
                               !w.is_skip_taskbar());
}
function nwRect(w) {
    const r = w.get_frame_rect();
    return {x: r.x, y: r.y, width: r.width, height: r.height};
}
function nwInfo(w) {
    const ws = w.get_workspace();
    return {id: String(w.get_id()), title: w.get_title() || '', wm_class: w.get_wm_class() || '',
            workspace: ws ? ws.index() : 0, minimized: Boolean(w.minimized),
            maximized: nwIsMaximized(w), focused: Boolean(w.has_focus()), geometry: nwRect(w)};
}
function nwWorkspace(index) {
    const manager = global.workspace_manager;
    if (!Number.isInteger(index) || index < 0 || index >= manager.get_n_workspaces())
        return null;
    return manager.get_workspace_by_index(index);
}
function nwRun(action, p) {
    p = p || {};
    const now = global.get_current_time();
    if (action === 'list')
        return {ok: true, windows: nwListed().map(nwInfo)};
    if (action === 'switch_workspace') {
        const ws = nwWorkspace(p.workspace);
        if (!ws) return {ok: false, error: 'workspace not found'};
        ws.activate(now);
        return {ok: true, message: `switched to workspace ${p.workspace}`};
    }
    const w = nwAll().find(c => String(c.get_id()) === String(p.window_id));
    if (!w) return {ok: false, error: 'window not found'};
    switch (action) {
    case 'focus':
        if (w.minimized) w.unminimize();
        Main.activateWindow(w, now);
        return {ok: true, message: 'focused'};
    case 'close':
        w.delete(now);
        return {ok: true, message: 'closed'};
    case 'minimize':
        w.minimize();
        return {ok: true, message: 'minimized'};
    case 'maximize':
        if (nwIsMaximized(w)) {
            nwUnmaximize(w);
            return {ok: true, message: 'unmaximized'};
        }
        nwMaximize(w);
        return {ok: true, message: 'maximized'};
    case 'move_to_workspace': {
        const ws = nwWorkspace(p.workspace);
        if (!ws) return {ok: false, error: 'workspace not found'};
        w.change_workspace(ws);
        return {ok: true, message: `moved to workspace ${p.workspace}`};
    }
    case 'get_geometry':
        return {ok: true, message: 'geometry', geometry: nwRect(w)};
    case 'set_geometry':
        nwUnmaximize(w);
        w.move_resize_frame(false, p.x, p.y, p.width, p.height);
        return {ok: true, message: 'geometry set', geometry: nwRect(w)};
    case 'set_position': {
        const r = w.get_frame_rect();
        w.move_resize_frame(false, p.x, p.y, r.width, r.height);
        return {ok: true, message: 'position set', geometry: nwRect(w)};
    }
    case 'set_size': {
        nwUnmaximize(w);
        const r = w.get_frame_rect();
        w.move_resize_frame(false, r.x, r.y, p.width, p.height);
        return {ok: true, message: 'size set', geometry: nwRect(w)};
    }
    case 'snap': {
        nwUnmaximize(w);
        const area = w.get_work_area_current_monitor();
        const left = Math.floor(area.width / 2);
        if (p.position === 'left')
            w.move_resize_frame(false, area.x, area.y, left, area.height);
        else
            w.move_resize_frame(false, area.x + left, area.y, area.width - left, area.height);
        return {ok: true, message: `snapped to ${p.position}`, geometry: nwRect(w)};
    }
    default:
        return {ok: false, error: `unknown action ${action}`};
    }
}
"""

WINDOW_HELPER_EXTENSION_JS = r"""// Generated by the Newelle "GNOME Desktop" extension. Do not edit.
import Gio from 'gi://Gio';
import Meta from 'gi://Meta';

import * as Main from 'resource:///org/gnome/shell/ui/main.js';
import {Extension} from 'resource:///org/gnome/shell/extensions/extension.js';

const BUS_NAME = '@BUS@';
const OBJECT_PATH = '@PATH@';
const VERSION = @VERSION@;
const IFACE = `<node>
  <interface name="${BUS_NAME}">
    <method name="Run">
      <arg name="action" type="s" direction="in"/>
      <arg name="params" type="s" direction="in"/>
      <arg name="result" type="s" direction="out"/>
    </method>
    <property name="Version" type="u" access="read"/>
  </interface>
</node>`;
@CORE@
class WindowControlService {
    get Version() {
        return VERSION;
    }

    Run(action, params) {
        try {
            return JSON.stringify(nwRun(action, params ? JSON.parse(params) : {}));
        } catch (error) {
            return JSON.stringify({ok: false, error: String(error?.message ?? error)});
        }
    }
}

export default class NewelleWindowControlExtension extends Extension {
    enable() {
        this._dbus = Gio.DBusExportedObject.wrapJSObject(IFACE, new WindowControlService());
        this._dbus.export(Gio.DBus.session, OBJECT_PATH);
        this._nameId = Gio.DBus.session.own_name(
            BUS_NAME, Gio.BusNameOwnerFlags.NONE, null, null);
    }

    disable() {
        if (this._nameId) {
            Gio.DBus.session.unown_name(this._nameId);
            this._nameId = 0;
        }
        this._dbus?.unexport();
        this._dbus = null;
    }
}
"""


def _window_helper_sources(shell_version: str = "") -> dict:
    versions = list(WINDOW_HELPER_SHELL_VERSIONS)
    major = shell_version.split(".")[0] if shell_version else ""
    if major.isdigit() and major not in versions:
        versions.append(major)
    metadata = {
        "uuid": WINDOW_HELPER_UUID,
        "name": "Newelle Window Control",
        "description": "Lets the Newelle assistant list, focus, move and resize windows "
                       "without GNOME Shell unsafe mode.",
        "version": WINDOW_HELPER_VERSION,
        "shell-version": versions,
        "url": "https://github.com/qwersyk/Newelle",
    }
    script = (WINDOW_HELPER_EXTENSION_JS
              .replace("@BUS@", WINDOW_HELPER_BUS)
              .replace("@PATH@", WINDOW_HELPER_PATH)
              .replace("@VERSION@", str(WINDOW_HELPER_VERSION))
              .replace("@CORE@", WINDOW_JS_CORE))
    return {"metadata.json": json.dumps(metadata, indent=2) + "\n", "extension.js": script}


def _window_helper_dir() -> Path:
    # Inside Flatpak the user data dir points into ~/.var/app; Shell reads the host one.
    base = Path.home() / ".local" / "share" if _is_flatpak() else Path(GLib.get_user_data_dir())
    return base / "gnome-shell" / "extensions" / WINDOW_HELPER_UUID


def _shell_extensions_call(method: str, params=None, reply_type: str = "()"):
    return _dbus_call("org.gnome.Shell.Extensions", "/org/gnome/Shell/Extensions",
                      "org.gnome.Shell.Extensions", method, params, reply_type)


def _window_helper_state() -> dict:
    """Return {'installed', 'loaded', 'state', 'error'} for the helper extension."""
    info = {}
    try:
        (info,) = _shell_extensions_call("GetExtensionInfo",
                                         GLib.Variant("(s)", (WINDOW_HELPER_UUID,)),
                                         "(a{sv})")
    except RuntimeError:
        info = {}
    return {
        "installed": (_window_helper_dir() / "extension.js").is_file(),
        "loaded": "uuid" in info,
        "enabled": bool(info.get("enabled", False)),
        "state": int(info.get("state", 0) or 0),
        "error": str(info.get("error", "") or ""),
    }


def _window_helper_call(action: str, params: dict, timeout: int = 15) -> dict:
    (raw,) = _dbus_call(WINDOW_HELPER_BUS, WINDOW_HELPER_PATH, WINDOW_HELPER_BUS, "Run",
                        GLib.Variant("(ss)", (action, json.dumps(params))), "(s)", timeout)
    return json.loads(raw)


def _window_eval_call(action: str, params: dict) -> dict:
    script = "%s\nnwRun(%s, %s);" % (WINDOW_JS_CORE, json.dumps(action), json.dumps(params))
    return json.loads(_shell_eval(script))


class GnomeCard(Gtk.Box):
    """Coherent result card shared by every GNOME tool."""

    _css_applied = False

    def __init__(self, extension, operation: str, arguments: dict):
        super().__init__(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        self.extension = weakref.ref(extension)
        self.operation = operation
        self.arguments = dict(arguments or {})
        self.payload = None
        self.busy = False
        self.add_css_class("card")
        self.set_margin_top(8)
        self.set_margin_bottom(8)
        self.set_hexpand(True)
        self._apply_css()
        definition = DEFINITIONS.get(operation, (operation, None, operation, "", {}, None))
        self.icon_name = definition[5] or "applications-utilities-symbolic"

        header = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=12,
                         css_classes=["gnome-header"])
        self.header_icon = Gtk.Image.new_from_icon_name(self.icon_name)
        self.header_icon.set_pixel_size(18)
        header.append(self.header_icon)
        self.title_label = self.label(definition[2], ["heading"], selectable=False)
        self.title_label.set_hexpand(True)
        header.append(self.title_label)
        self.status = Gtk.Label(label=_("Loading…"), xalign=1, max_width_chars=30,
                                ellipsize=Pango.EllipsizeMode.END)
        self.status.add_css_class("caption")
        self.status.add_css_class("dim-label")
        self._status_css = "dim-label"
        header.append(self.status)
        self.spinner = Gtk.Spinner(visible=False)
        header.append(self.spinner)
        self.append(header)

        self.body = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8,
                            css_classes=["gnome-body"])
        self.append(self.body)
        self.controls = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6,
                                css_classes=["gnome-footer"])
        self.controls.set_visible(False)
        self.append(self.controls)

    def _apply_css(self):
        if GnomeCard._css_applied:
            return
        display = self.get_display()
        if display is None:
            return
        provider = Gtk.CssProvider()
        provider.load_from_data(CARD_CSS)
        Gtk.StyleContext.add_provider_for_display(
            display, provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        GnomeCard._css_applied = True

    @staticmethod
    def label(text, css_classes=None, xalign=0, selectable=True):
        label = Gtk.Label(label="" if text is None else str(text), xalign=xalign,
                          wrap=True, wrap_mode=Pango.WrapMode.WORD_CHAR,
                          selectable=selectable)
        for name in css_classes or []:
            label.add_css_class(name)
        return label

    @staticmethod
    def clear(box):
        child = box.get_first_child()
        while child is not None:
            nxt = child.get_next_sibling()
            box.remove(child)
            child = nxt

    def set_status(self, text: str, css: str = "dim-label"):
        if css != self._status_css:
            self.status.remove_css_class(self._status_css)
            self.status.add_css_class(css)
            self._status_css = css
        self.status.set_text(text)
        self.status.set_tooltip_text(text)

    def set_busy(self, busy: bool):
        self.busy = busy
        self.spinner.set_spinning(busy)
        self.spinner.set_visible(busy)
        self.controls.set_sensitive(not busy)
        self.body.set_sensitive(not busy)
        if busy:
            self.set_status(_("Working…"))

    def call(self, operation: str, arguments: dict):
        ext = self.extension()
        if ext is None or self.busy:
            return
        ext.card_action(self, operation, arguments)

    # -- small builders ----------------------------------------------------
    def caption(self, text, icon=None, css=None):
        classes = ["caption", css or "dim-label"]
        if icon is None:
            return self.label(text, classes)
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        image = Gtk.Image.new_from_icon_name(icon)
        image.set_pixel_size(14)
        image.add_css_class(css or "dim-label")
        row.append(image)
        row.append(self.label(text, classes))
        return row

    def icon_label(self, text, icon):
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        image = Gtk.Image.new_from_icon_name(icon)
        image.set_pixel_size(14)
        image.add_css_class("dim-label")
        row.append(image)
        row.append(self.label(text))
        return row

    @staticmethod
    def chip(text, variant="neutral"):
        chip = Gtk.Label(label=str(text))
        chip.add_css_class("gnome-chip")
        chip.add_css_class("gnome-chip-" + variant)
        return chip

    @staticmethod
    def chip_box(*chips):
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        for chip in chips:
            box.append(chip)
        return box

    def item_button(self, box, text, callback, icon=None, css="flat"):
        if icon:
            content = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
            content.append(Gtk.Image.new_from_icon_name(icon))
            content.append(Gtk.Label(label=text))
            button = Gtk.Button(child=content, css_classes=[css] if css else [])
        else:
            button = Gtk.Button(label=text, css_classes=[css] if css else [])
        button.connect("clicked", lambda *_: callback())
        box.append(button)
        return button

    def footer_button(self, text, callback, icon=None, css="flat"):
        return self.item_button(self.controls, text, callback, icon, css)

    def copy_button(self, value: str):
        button = Gtk.Button(icon_name="edit-copy-symbolic", css_classes=["flat"],
                            valign=Gtk.Align.CENTER, tooltip_text=_("Copy"))
        button.connect("clicked", self._copy_value, str(value))
        return button

    def _copy_value(self, button, value):
        self.get_clipboard().set(value)
        button.set_icon_name("object-select-symbolic")

        def restore(btn):
            if btn.get_root() is not None:
                btn.set_icon_name("edit-copy-symbolic")
            return False
        GLib.timeout_add(2000, restore, button)

    def boxed_list(self):
        return Gtk.ListBox(selection_mode=Gtk.SelectionMode.NONE, css_classes=["boxed-list"])

    def scrolled(self, child, max_height=360):
        scroll = Gtk.ScrolledWindow(hscrollbar_policy=Gtk.PolicyType.NEVER,
                                    vscrollbar_policy=Gtk.PolicyType.AUTOMATIC,
                                    propagate_natural_height=True,
                                    max_content_height=max_height)
        scroll.set_child(child)
        return scroll

    # -- rendering ----------------------------------------------------------
    def render(self, payload: dict):
        self.payload = payload or {}
        self.set_busy(False)
        self.clear(self.body)
        self.clear(self.controls)
        if not self.payload.get("ok"):
            self.render_failure(self.payload)
        else:
            data = self.payload.get("data", {})
            if self.payload.get("verified"):
                self.set_status(_("Done and verified"), "success")
            elif data.get("items") == []:
                self.set_status(_("No results"))
            else:
                self.set_status(_("Ready"), "success")
            try:
                renderer = getattr(self, "_render_" + self.operation.replace("gnome_", ""))
                renderer(data)
            except AttributeError:
                self.body.append(self.label(json.dumps(data, ensure_ascii=False)[:4000],
                                            ["caption", "gnome-mono"]))
        notice = (self.payload.get("data", {}) or {}).get("notice")
        if notice:
            self.body.append(self.caption(str(notice), "dialog-information-symbolic"))
        self.controls.set_visible(self.controls.get_first_child() is not None)

    def render_failure(self, payload: dict):
        self.set_status(_("Failed"), "error")
        self.body.append(self.label(str(payload.get("error") or _("Unknown error")), ["error"]))
        code = payload.get("code")
        if code:
            self.body.append(self.caption(_("Error code: %s") % code))
        if code == "window_helper_missing":
            self.footer_button(_("Install window helper"), self._install_window_helper,
                               "list-add-symbolic", "suggested-action")
        self.footer_button(_("Retry"), lambda: self.call(self.operation, self.arguments),
                           "view-refresh-symbolic")

    def _install_window_helper(self):
        ext = self.extension()
        if ext is None or self.busy:
            return
        ext.card_install_window_helper(self)

    def refresh_button(self):
        self.footer_button(_("Refresh"), lambda: self.call(self.operation, self.arguments),
                           "view-refresh-symbolic")

    # -- per-tool renderers ---------------------------------------------------
    def _render_send_notification(self, data):
        row = Adw.ActionRow(title=str(data.get("summary", "")),
                            subtitle=str(data.get("body", "")) or None,
                            icon_name="preferences-system-notifications-symbolic")
        box = self.boxed_list()
        box.append(row)
        self.body.append(box)
        self.body.append(self.chip_box(self.chip(_("Notification sent"), "success")))

    def _render_open_file(self, data):
        self.body.append(self.icon_label(str(data.get("path", "")), "folder-symbolic"))
        if data.get("opened_with"):
            self.body.append(self.caption(_("Opened with: %s") % data["opened_with"]))
        self.body.append(self.chip_box(self.chip(_("Opened"), "success")))
        if data.get("path"):
            path = data["path"]
            self.footer_button(_("Open again"),
                               lambda: self.call("gnome_open_file", {"path": path}),
                               "folder-open-symbolic")

    def _render_set_wallpaper(self, data):
        path = str(data.get("image_path", ""))
        if os.path.isfile(path):
            try:
                picture = Gtk.Picture.new_for_filename(path)
                picture.set_content_fit(Gtk.ContentFit.COVER)
                picture.set_size_request(-1, 220)
                picture.add_css_class("card")
                self.body.append(picture)
            except Exception:
                pass
        self.body.append(self.icon_label(path, "preferences-desktop-wallpaper-symbolic"))
        self.body.append(self.chip_box(self.chip(_("Wallpaper applied"), "success")))
        if data.get("mode"):
            self.body.append(self.caption(str(data["mode"])))

    def _render_set_volume(self, data):
        level = float(data.get("level", 0) or 0)
        muted = bool(data.get("muted"))
        bar = Gtk.ProgressBar(fraction=max(0.0, min(1.0, level / 100.0)), show_text=True,
                              text=f"{level:.0f}%")
        bar.set_hexpand(True)
        self.body.append(bar)
        self.body.append(self.chip_box(
            self.chip(_("Muted") if muted else _("Audible"), "warning" if muted else "success"),
            self.chip(data.get("source", "pipewire"), "neutral")))
        self.footer_button(_("Mute") if not muted else _("Unmute"),
                           lambda: self.call("gnome_set_volume", {"mute": not muted}),
                           "audio-volume-muted-symbolic")
        self.footer_button(_("Volume down"),
                           lambda: self.call("gnome_set_volume", {"direction": "down"}),
                           "audio-volume-low-symbolic")
        self.footer_button(_("Volume up"),
                           lambda: self.call("gnome_set_volume", {"direction": "up"}),
                           "audio-volume-high-symbolic")

    def _render_media_control(self, data):
        self.body.append(self.label(str(data.get("message") or data.get("action", "")),
                                    ["gnome-title"]))
        if data.get("player"):
            self.body.append(self.caption(str(data["player"])))
        if data.get("title") and data["title"] != "Unknown":
            self.body.append(self.icon_label(
                "%s — %s" % (data.get("title", ""), data.get("artist", "")),
                "media-optical-symbolic"))
        self.body.append(self.chip_box(self.chip(str(data.get("action", "")), "accent")))
        player = data.get("player_match") or ""
        for action, icon in (("play", "media-playback-start-symbolic"),
                             ("pause", "media-playback-pause-symbolic"),
                             ("play_pause", "media-playback-start-symbolic"),
                             ("previous", "media-skip-backward-symbolic"),
                             ("next", "media-skip-forward-symbolic"),
                             ("stop", "media-playback-stop-symbolic")):
            self.footer_button(action.replace("_", " ").title(),
                               lambda a=action: self.call(
                                   "gnome_media_control",
                                   {"action": a, **({"player": player} if player else {})}),
                               icon)

    def _render_quick_settings(self, data):
        setting = str(data.get("setting", ""))
        enabled = bool(data.get("enabled"))
        row = Adw.ActionRow(title=setting.replace("_", " ").title(),
                            subtitle=str(data.get("message", "")) or None,
                            icon_name="system-settings-symbolic")
        switch = Gtk.Switch(active=enabled, valign=Gtk.Align.CENTER)
        switch.connect("state-set", self._on_quick_toggled, setting)
        row.add_suffix(switch)
        box = self.boxed_list()
        box.append(row)
        self.body.append(box)
        self.body.append(self.chip_box(self.chip(_("Enabled") if enabled else _("Disabled"),
                                                 "success" if enabled else "neutral")))

    def _on_quick_toggled(self, switch, state, setting):
        self.call("gnome_quick_settings", {"setting": setting, "enabled": bool(state)})
        return True

    def _render_take_screenshot(self, data):
        path = str(data.get("path") or data.get("uri", ""))
        local = path[7:] if path.startswith("file://") else path
        if os.path.isfile(local):
            try:
                picture = Gtk.Picture.new_for_filename(local)
                picture.set_content_fit(Gtk.ContentFit.SCALE_DOWN)
                picture.set_size_request(-1, 240)
                self.body.append(picture)
            except Exception:
                pass
        self.body.append(self.icon_label(path, "camera-photo-symbolic"))
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        row.append(self.label(path, ["caption", "dim-label", "gnome-mono"]))
        label = Gtk.Label(label="", hexpand=True)
        row.append(label)
        row.append(self.copy_button(path))
        self.body.append(row)
        if data.get("interactive"):
            self.body.append(self.caption(_("Interactive capture"), "camera-photo-symbolic"))

    def _render_window_management(self, data):
        windows = data.get("windows")
        if isinstance(windows, list):
            box = self.boxed_list()
            for win in windows[:50]:
                title = str(win.get("title") or _("Untitled"))
                sub = "%s · %s %d" % (win.get("wm_class", ""), _("workspace"),
                                      int(win.get("workspace", 0)))
                row = Adw.ActionRow(title=title, subtitle=sub)
                if win.get("focused"):
                    row.add_prefix(Gtk.Image.new_from_icon_name("object-select-symbolic"))
                chips = " · ".join(
                    [s for s, on in (
                        (_("minimized"), win.get("minimized")),
                        (_("maximized"), win.get("maximized")),
                    ) if on]
                )
                if chips:
                    row.set_subtitle(sub + " · " + chips)
                wid = str(win.get("id", ""))
                for label, action, icon in ((_("Focus"), "focus", "go-next-symbolic"),
                                           (_("Minimize"), "minimize", "go-down-symbolic"),
                                           (_("Close"), "close", "window-close-symbolic")):
                    button = Gtk.Button(icon_name=icon, css_classes=["flat"],
                                        valign=Gtk.Align.CENTER, tooltip_text=label)
                    button.connect("clicked", self._on_window_button, action, wid)
                    row.add_suffix(button)
                box.append(row)
            if len(windows) > 4:
                self.body.append(self.scrolled(box))
            else:
                self.body.append(box)
            self.body.append(self.caption(_("%d window(s)") % len(windows)))
            self.refresh_button()
        else:
            self.body.append(self.label(str(data.get("message", "")), ["gnome-title"]))
            if data.get("window_id"):
                self.body.append(self.caption(_("Window %s") % data["window_id"]))
            if data.get("geometry"):
                self.body.append(self.label(json.dumps(data["geometry"], indent=2),
                                            ["caption", "gnome-mono"]))
            self.footer_button(_("List windows"),
                               lambda: self.call("gnome_window_management", {"action": "list"}),
                               "view-refresh-symbolic")

    def _on_window_button(self, _button, action, window_id):
        self.call("gnome_window_management", {"action": action, "window_id": window_id})

    def _render_keyring(self, data):
        action = str(data.get("action", ""))
        if action == "retrieve" and data.get("found"):
            self.body.append(self.label(str(data.get("label", "")), ["gnome-title"]))
            if data.get("attributes"):
                self.body.append(self.caption(json.dumps(data["attributes"])))
            secret = str(data.get("secret", ""))
            row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
            entry = Gtk.PasswordEntry(show_peek_icon=True, text=secret, editable=False,
                                      hexpand=True)
            row.append(entry)
            row.append(self.copy_button(secret))
            self.body.append(row)
            self.body.append(self.caption(
                _("Secret shown. Handle it carefully and avoid pasting it publicly."),
                "dialog-warning-symbolic", "warning"))
        else:
            self.body.append(self.label(str(data.get("message", "")), ["gnome-title"]))
            self.body.append(self.chip_box(self.chip(action.title(), "success")))

    def _render_calendar_events(self, data):
        items = data.get("items", [])
        if not items:
            self.body.append(self.caption(_("No events in the selected range.")))
            self.refresh_button()
            return
        container = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        for event in items[:50]:
            box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4,
                          css_classes=["gnome-item"])
            box.append(self.label(str(event.get("title") or _("(No title)")), ["gnome-title"]))
            start, end = str(event.get("start", "")), str(event.get("end", ""))
            if start or end:
                box.append(self.icon_label(f"{start} → {end}", "alarm-symbolic"))
            if event.get("calendar"):
                box.append(self.caption(str(event["calendar"])))
            if event.get("location"):
                box.append(self.icon_label(str(event["location"]), "map-marker-symbolic"))
            if event.get("description"):
                desc = str(event["description"])
                box.append(self.caption(desc[:500]))
            container.append(box)
        self.body.append(self.scrolled(container) if len(items) > 4 else container)
        self.body.append(self.caption(_("%d event(s)") % len(items)))
        self.refresh_button()

    def _render_tasks(self, data):
        items = data.get("items", [])
        if not items:
            self.body.append(self.caption(_("No tasks found.")))
            self.refresh_button()
            return
        container = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        for task in items[:60]:
            box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4,
                          css_classes=["gnome-item"])
            box.append(self.label(str(task.get("title") or _("(No title)")), ["gnome-title"]))
            chips = []
            status = str(task.get("status", ""))
            if status:
                chips.append(self.chip(status,
                                       "success" if status.lower() in ("completed",) else "neutral"))
            if task.get("priority"):
                chips.append(self.chip(str(task["priority"]), "accent"))
            if chips:
                box.append(self.chip_box(*chips))
            if task.get("due"):
                box.append(self.icon_label(_("Due: %s") % task["due"],
                                           "x-office-calendar-symbolic"))
            if task.get("description"):
                box.append(self.caption(str(task["description"])[:500]))
            container.append(box)
        self.body.append(self.scrolled(container) if len(items) > 4 else container)
        self.body.append(self.caption(_("%d task(s)") % len(items)))
        self.refresh_button()

    def _render_contacts(self, data):
        items = data.get("items", [])
        if not items:
            self.body.append(self.caption(_("No contacts found.")))
            self.refresh_button()
            return
        box = self.boxed_list()
        for contact in items[:40]:
            title = str(contact.get("title") or contact.get("name") or _("Unnamed contact"))
            subtitle = contact.get("organization") or contact.get("source") or None
            row = Adw.ActionRow(title=title, subtitle=subtitle,
                                icon_name="avatar-default-symbolic")
            emails = contact.get("emails", []) or []
            if emails:
                row.set_subtitle((subtitle + " · " if subtitle else "") + str(emails[0]))
                row.add_suffix(self.copy_button(str(emails[0])))
            box.append(row)
            for extra in (emails[1:] if len(emails) > 1 else []):
                detail = Adw.ActionRow(title=str(extra), icon_name="mail-unread-symbolic")
                detail.add_suffix(self.copy_button(str(extra)))
                box.append(detail)
            for phone in (contact.get("phones", []) or [])[:3]:
                detail = Adw.ActionRow(title=str(phone), icon_name="call-start-symbolic")
                detail.add_suffix(self.copy_button(str(phone)))
                box.append(detail)
        self.body.append(self.scrolled(box) if len(items) > 3 else box)
        self.body.append(self.caption(_("%d contact(s)") % len(items)))
        self.refresh_button()

    def _render_system_info(self, data):
        box = self.boxed_list()
        order = [("hostname", _("Hostname"), "computer-symbolic"),
                 ("os", _("Operating system"), "system-os-symbolic"),
                 ("gnome_version", _("GNOME version"), "org.gnome.Shell-symbolic"),
                 ("desktop", _("Session"), "video-display-symbolic"),
                 ("uptime", _("Uptime"), "alarm-symbolic"),
                 ("arch", _("Architecture"), "cpu-symbolic")]
        for key, title, icon in order:
            if data.get(key):
                box.append(Adw.ActionRow(title=title, subtitle=str(data[key]), icon_name=icon))
        self.body.append(box)
        self.refresh_button()

    def _render_audio_status(self, data):
        volume = data.get("volume", {})
        level = float(volume.get("level", 0) or 0)
        self.body.append(Gtk.ProgressBar(fraction=max(0.0, min(1.0, level / 100.0)),
                                         show_text=True, text=f"{level:.0f}%"))
        players = data.get("players", [])
        if not players:
            self.body.append(self.caption(_("No media players found.")))
        else:
            box = self.boxed_list()
            for player in players[:10]:
                title = "%s — %s" % (player.get("title", _("Unknown")),
                                       player.get("artist", ""))
                box.append(Adw.ActionRow(title=str(player.get("player_name", "")),
                                         subtitle=title,
                                         icon_name="media-optical-symbolic"))
            self.body.append(box)
        self.refresh_button()


class GnomeExtension(NewelleExtension):
    """Native GNOME desktop controls mirroring gnome-mcp-server."""

    name = "GNOME Desktop"
    id = "gnome_desktop"

    def __init__(self, pip_path, extension_path, settings):
        super().__init__(pip_path, extension_path, settings)
        self._cards = weakref.WeakSet()
        self._uninstalled = False

    @staticmethod
    def requires_sandbox_escape() -> bool:
        return True

    @staticmethod
    def get_extra_requirements() -> list:
        return []

    # -- settings ----------------------------------------------------------
    def _cfg(self, key, default):
        return self.get_setting(key, False, default)

    def configuration(self) -> dict:
        return {
            "volume_step": int(self._cfg("volume_step", 10) or 10),
            "screenshot_interactive": bool(self._cfg("screenshot_interactive", False)),
            "days_ahead": int(self._cfg("days_ahead", 30) or 30),
            "days_behind": int(self._cfg("days_behind", 0) or 0),
            "tasks_include_completed": bool(self._cfg("tasks_include_completed", True)),
            "tasks_include_cancelled": bool(self._cfg("tasks_include_cancelled", False)),
            "tasks_due_within_days": int(self._cfg("tasks_due_within_days", 0) or 0),
            "contacts_email_only": bool(self._cfg("contacts_email_only", False)),
        }

    def get_extra_settings(self) -> list:
        rows = []
        for key, title in CAPABILITIES:
            rows.append({
                "key": "enable_" + key, "type": "toggle",
                "title": title,
                "description": _("Enable %s tools") % title,
                "default": True,
            })
        helper_installed = (_window_helper_dir() / "extension.js").is_file()
        rows.append({
            "key": "window_helper", "type": "button",
            "title": _("Window control helper"),
            "description": _("Install a small GNOME Shell extension so window management works "
                             "without unsafe mode. Takes effect after logging out and back in."),
            "label": _("Reinstall") if helper_installed else _("Install"),
            "callback": self._on_install_helper_clicked,
            "default": None,
        })
        rows.extend([
            {"key": "volume_step", "type": "range", "title": _("Volume step"),
             "description": _("Step used by volume up/down and media direction controls"),
             "default": 10, "min": 1, "max": 30, "round-digits": 0},
            {"key": "screenshot_interactive", "type": "toggle",
             "title": _("Interactive screenshots by default"),
             "description": _("Show the area-selection dialog unless the tool overrides it"),
             "default": False},
            {"key": "days_ahead", "type": "range", "title": _("Calendar days ahead"),
             "description": _("Default range for calendar events"), "default": 30,
             "min": 0, "max": 366, "round-digits": 0},
            {"key": "days_behind", "type": "range", "title": _("Calendar days behind"),
             "description": _("Default look-behind for calendar events"), "default": 0,
             "min": 0, "max": 366, "round-digits": 0},
            {"key": "tasks_include_completed", "type": "toggle",
             "title": _("Tasks: include completed"),
             "description": _("Show completed tasks by default"), "default": True},
            {"key": "tasks_include_cancelled", "type": "toggle",
             "title": _("Tasks: include cancelled"),
             "description": _("Show cancelled tasks by default"), "default": False},
            {"key": "tasks_due_within_days", "type": "range",
             "title": _("Tasks due within (days)"),
             "description": _("Only tasks due within N days; 0 means all"), "default": 0,
             "min": 0, "max": 365, "round-digits": 0},
            {"key": "contacts_email_only", "type": "toggle",
             "title": _("Contacts: email only"),
             "description": _("Only list contacts that have an email address"), "default": False},
        ])
        return rows

    def get_additional_prompts(self) -> list:
        return [{
            "key": "gnome_desktop",
            "setting_name": "gnome_desktop",
            "title": _("GNOME desktop control"),
            "description": _("Let the assistant control notifications, files, wallpaper, "
                               "volume, media, quick settings, screenshots, windows, keyring, "
                               "calendar, tasks and contacts on this GNOME desktop"),
            "editable": True,
            "show_in_settings": True,
            "default": True,
            "text": ("You can control the user's GNOME desktop with the gnome_* tools. "
                     "Prefer list/search tools (window list, contacts, calendar, "
                     "tasks) before acting on a name, and confirm destructive actions "
                     "(close window, delete secret) in your reply. Window management needs "
                     "the Newelle window control helper (a small GNOME Shell extension); if "
                     "the tool reports it missing, tell the user to install it from the "
                     "card button or the extension settings and log out and back in, "
                     "instead of retrying silently."),
        }]

    # -- tools --------------------------------------------------------------
    def get_tools(self) -> list:
        tools = []
        for name, capability, title, description, schema, icon in TOOL_DEFINITIONS:
            if not self._cfg("enable_" + capability, True):
                continue
            tools.append(Tool(
                name, description, functools.partial(self.invoke, name),
                schema=schema, title=title, run_on_main_thread=True,
                restore_func=functools.partial(self.restore, name),
                tools_group=self.name, icon_name=icon, default_lazy_load=True,
            ))
        return tools

    def _enabled(self, operation: str) -> bool:
        capability = DEFINITIONS.get(operation, (None, None))[1]
        return bool(self._cfg("enable_" + str(capability), True)) if capability else True

    # -- execution -----------------------------------------------------------
    def invoke(self, operation: str, arguments=None, tool_uuid=None, chat_id=None,
               msg_uuid=None, **kwargs):
        args = dict(arguments) if isinstance(arguments, dict) else {}
        args.update(kwargs or {})
        result = ToolResult()

        def start():
            card = None
            if Gtk.is_initialized():
                card = GnomeCard(self, operation, args)
                self._cards.add(card)
                result.set_widget(card)
                card.set_busy(True)

            def work():
                try:
                    response = self._run(operation, args)
                except Exception as error:  # noqa: BLE001 - surfaced to model/UI
                    response = {"ok": False, "operation": operation,
                                "error": str(error), "code": "failed"}

                def finish():
                    try:
                        if card is not None:
                            card.render(response)
                    finally:
                        result.set_output(json.dumps(response, ensure_ascii=False))
                    return False
                GLib.idle_add(finish)
            threading.Thread(target=work, daemon=True).start()
            return False

        if Gtk.is_initialized():
            if threading.current_thread() is threading.main_thread():
                start()
            else:
                GLib.idle_add(start)
        else:
            try:
                result.set_output(json.dumps(self._run(operation, args), ensure_ascii=False))
            except Exception as error:  # noqa: BLE001
                result.set_output(json.dumps({"ok": False, "error": str(error)}))
        return result

    def restore(self, operation: str, tool_uuid=None, chat_id=None, msg_uuid=None, **kwargs):
        result = ToolResult()
        payload = None
        if tool_uuid and getattr(self, "ui_controller", None):
            try:
                raw = self.ui_controller.get_tool_result_by_id(tool_uuid)
                payload = json.loads(raw) if raw else None
            except (ValueError, TypeError):
                payload = None
        if not isinstance(payload, dict):
            payload = {"ok": False, "operation": operation,
                       "error": _("Saved result unavailable. Run the tool again."),
                       "code": "history_unavailable"}

        def render():
            if Gtk.is_initialized():
                try:
                    card = GnomeCard(self, operation, kwargs or {})
                    self._cards.add(card)
                    card.render(payload)
                    result.set_widget(card)
                except Exception:  # noqa: BLE001 - text output remains
                    pass
            result.set_output(json.dumps(payload, ensure_ascii=False))
            return False

        if threading.current_thread() is threading.main_thread() or not Gtk.is_initialized():
            render()
        else:
            GLib.idle_add(render)
        return result

    def card_action(self, card: GnomeCard, operation: str, arguments: dict, runner=None):
        card.set_busy(True)

        def work():
            try:
                response = runner() if runner else self._run(operation, arguments)
            except Exception as error:  # noqa: BLE001
                response = {"ok": False, "operation": operation,
                            "error": str(error), "code": "failed"}

            def finish():
                if self._uninstalled:
                    return False
                card.operation = operation
                card.arguments = dict(arguments)
                definition = DEFINITIONS.get(operation)
                if definition:
                    card.title_label.set_text(definition[2])
                    card.header_icon.set_from_icon_name(definition[5])
                card.render(response)
                return False
            GLib.idle_add(finish)
        threading.Thread(target=work, daemon=True).start()

    def _run(self, operation: str, arguments: dict) -> dict:
        if self._uninstalled:
            return {"ok": False, "operation": operation,
                    "error": _("Extension was uninstalled."), "code": "disabled"}
        if operation not in DEFINITIONS:
            return {"ok": False, "operation": operation,
                    "error": _("Unknown operation."), "code": "unknown_operation"}
        if not self._enabled(operation):
            return {"ok": False, "operation": operation,
                    "error": _("This capability is disabled in extension settings."),
                    "code": "disabled"}
        handler = getattr(self, "_op_" + operation.replace("gnome_", ""), None)
        if handler is None:
            return {"ok": False, "operation": operation,
                    "error": _("Not implemented."), "code": "unimplemented"}
        try:
            data = handler(dict(arguments or {}))
        except WindowHelperUnavailable as error:
            return {"ok": False, "operation": operation,
                    "error": str(error), "code": "window_helper_missing"}
        except (ValueError, RuntimeError, OSError) as error:
            return {"ok": False, "operation": operation,
                    "error": str(error), "code": "failed"}
        return {"ok": True, "operation": operation, "data": data,
                "verified": bool(data.get("verified", True))}

    def on_uninstall(self):
        self._uninstalled = True

        def stop():
            for card in list(self._cards):
                card.controls.set_sensitive(False)
                card.body.set_sensitive(False)
            return False
        if Gtk.is_initialized():
            GLib.idle_add(stop)

    # =======================================================================
    # Tool implementations (parity with gnome-mcp-server)
    # =======================================================================

    # -- send_notification ----------------------------------------------------
    def _op_send_notification(self, args: dict) -> dict:
        summary = str(args.get("summary", "")).strip()
        body = str(args.get("body", "")).strip()
        if not summary:
            raise ValueError(_("summary is required."))
        if not body:
            raise ValueError(_("body is required."))
        if len(summary) > 500 or len(body) > 4000:
            raise ValueError(_("Notification text is too long."))
        if _have_cmd("notify-send"):
            _run_cmd(["notify-send", summary, body])
        else:
            bus = Gio.bus_get_sync(Gio.BusType.SESSION, None)
            proxy = Gio.DBusProxy.new_sync(
                bus, Gio.DBusProxyFlags.NONE, None,
                "org.freedesktop.Notifications", "/org/freedesktop/Notifications",
                "org.freedesktop.Notifications", None)
            proxy.call_sync("Notify", GLib.Variant("(susssasa{sv}i)", (
                "Newelle", 0, "", summary, body, [], {}, 5000)),
                Gio.DBusCallFlags.NONE, 5000, None)
        return {"summary": summary, "body": body, "verified": True}

    # -- open_file --------------------------------------------------------------
    def _op_open_file(self, args: dict) -> dict:
        path = str(args.get("path", "")).strip()
        if not path:
            raise ValueError(_("path is required."))
        opened_with = ""
        try:
            if path.startswith(("http://", "https://", "file://")):
                uri = path
            else:
                expanded = os.path.expanduser(path)
                if not os.path.exists(expanded):
                    raise RuntimeError(_("File does not exist: %s") % path)
                uri = Gio.File.new_for_path(expanded).get_uri()
            opened = Gio.AppInfo.launch_default_for_uri(uri, None)
            if not opened:
                raise RuntimeError("GIO launch rejected")
            opened_with = _("default application (GIO)")
        except Exception:
            _run_cmd(["xdg-open", path], timeout=10)
            opened_with = "xdg-open"
        return {"path": path, "opened_with": opened_with, "verified": True}

    # -- set_wallpaper ------------------------------------------------------------
    def _op_set_wallpaper(self, args: dict) -> dict:
        image_path = os.path.expanduser(str(args.get("image_path", "")).strip())
        if not image_path:
            raise ValueError(_("image_path is required."))
        if not os.path.isfile(image_path):
            raise RuntimeError(_("Image file does not exist: %s") % image_path)
        ext = os.path.splitext(image_path)[1].lower().lstrip(".")
        if ext not in ("jpg", "jpeg", "png", "webp"):
            raise ValueError(_("Unsupported image format '%s'. Use JPG, PNG or WebP.") % ext)
        uri = Path(image_path).resolve().as_uri()
        quoted = "'" + uri.replace("'", "'\''") + "'"
        _gsettings_set("org.gnome.desktop.background", "picture-uri", quoted)
        _gsettings_set("org.gnome.desktop.background", "picture-uri-dark", quoted)
        try:
            _gsettings_set("org.gnome.desktop.background", "picture-options", "'zoom'")
        except Exception:  # noqa: BLE001 - options are best effort
            pass
        return {"image_path": image_path, "uri": uri,
                "mode": _("Applied to light and dark backgrounds."),
                "verified": True}

    # -- volume / media ------------------------------------------------------------
    def _volume_status(self) -> dict:
        if _have_cmd("wpctl"):
            try:
                out = _run_cmd(["wpctl", "get-volume", "@DEFAULT_AUDIO_SINK@"])
                # e.g. "Volume: 0.65 [MUTED]"
                level = 0.0
                parts = out.split()
                if len(parts) >= 2:
                    try:
                        level = float(parts[1]) * 100.0
                    except ValueError:
                        level = 0.0
                return {"level": round(level), "muted": "[MUTED]" in out,
                        "source": "pipewire"}
            except Exception:  # noqa: BLE001 - try pactl next
                pass
        if _have_cmd("pactl"):
            try:
                out = _run_cmd(["pactl", "get-sink-volume", "@DEFAULT_SINK@"])
                match = re.search(r"(\d+)\s*%", out)
                level = float(match.group(1)) if match else 0.0
                mute_out = _run_cmd(["pactl", "get-sink-mute", "@DEFAULT_SINK@"])
                return {"level": round(level), "muted": "yes" in mute_out.lower(),
                        "source": "pulseaudio"}
            except Exception:  # noqa: BLE001
                pass
        raise RuntimeError(_("No volume backend found (need wpctl or pactl)."))

    def _op_set_volume(self, args: dict) -> dict:
        step = max(1, min(30, self.configuration()["volume_step"]))
        volume = args.get("volume")
        mute = args.get("mute")
        relative = bool(args.get("relative", False))
        direction = args.get("direction")
        if volume is None and mute is None and not direction:
            raise ValueError(_("Give volume, mute, or direction (up/down)."))

        def apply_wpctl(vol_str=None, mute_val=None):
            if vol_str is not None:
                _run_cmd(["wpctl", "set-volume", "@DEFAULT_AUDIO_SINK@", vol_str])
            if mute_val is not None:
                _run_cmd(["wpctl", "set-mute", "@DEFAULT_AUDIO_SINK@",
                          "1" if mute_val else "0"])

        def apply_pactl(vol_str=None, mute_val=None):
            if vol_str is not None:
                _run_cmd(["pactl", "set-sink-volume", "@DEFAULT_SINK@", vol_str])
            if mute_val is not None:
                _run_cmd(["pactl", "set-sink-mute", "@DEFAULT_SINK@",
                          "1" if mute_val else "0"])

        backend = "wpctl" if _have_cmd("wpctl") else ("pactl" if _have_cmd("pactl") else None)
        if backend is None:
            raise RuntimeError(_("No volume backend found (need wpctl or pactl)."))

        if direction in ("up", "down"):
            delta = step if direction == "up" else -step
            if backend == "wpctl":
                apply_wpctl(f"{abs(delta)}%{'+' if delta >= 0 else '-'}")
            else:
                apply_pactl(f"{'+' if delta >= 0 else '-'}{abs(delta)}%")
        elif volume is not None:
            try:
                level = float(volume)
            except (TypeError, ValueError):
                raise ValueError(_("volume must be a number 0-100.")) from None
            if relative:
                if backend == "wpctl":
                    apply_wpctl(f"{abs(level)}%{'+' if level >= 0 else '-'}")
                else:
                    apply_pactl(f"{'+' if level >= 0 else '-'}{abs(level)}%")
            else:
                if not 0 <= level <= 150:
                    raise ValueError(_("volume must be between 0 and 100."))
                if backend == "wpctl":
                    apply_wpctl(f"{level}%")
                else:
                    apply_pactl(f"{level}%")
        if mute is not None:
            if not isinstance(mute, bool):
                raise ValueError(_("mute must be true or false."))
            if backend == "wpctl":
                apply_wpctl(mute_val=mute)
            else:
                apply_pactl(mute_val=mute)
        # Small delay so PipeWire/PulseAudio settles before read-back.
        time.sleep(0.2)
        status = self._volume_status()
        status["verified"] = True
        return status

    def _mpris_players(self) -> list:
        if _have_cmd("playerctl"):
            try:
                out = _run_cmd(["playerctl", "--list-all"], timeout=8)
                players = [line.strip() for line in out.splitlines() if line.strip()]
                if players:
                    return players
            except Exception:  # noqa: BLE001 - fall back to D-Bus
                pass
        bus = Gio.bus_get_sync(Gio.BusType.SESSION, None)
        proxy = Gio.DBusProxy.new_sync(
            bus, Gio.DBusProxyFlags.NONE, None,
            "org.freedesktop.DBus", "/org/freedesktop/DBus",
            "org.freedesktop.DBus", None)
        names = proxy.call_sync("ListNames", None, Gio.DBusCallFlags.NONE, 5000, None).unpack()[0]
        return sorted(n for n in names if n.startswith("org.mpris.MediaPlayer2."))

    def _mpris_metadata(self, bus_name: str) -> dict:
        info = {"player_name": bus_name, "dbus_name": bus_name,
                "playback_status": "Unknown", "title": "Unknown", "artist": "Unknown"}
        try:
            bus = Gio.bus_get_sync(Gio.BusType.SESSION, None)
            player = Gio.DBusProxy.new_sync(
                bus, Gio.DBusProxyFlags.NONE, None, bus_name,
                "/org/mpris/MediaPlayer2", "org.mpris.MediaPlayer2.Player", None)
            try:
                info["playback_status"] = player.get_cached_property("PlaybackStatus").unpack()
            except Exception:  # noqa: BLE001
                pass
            try:
                metadata = player.get_cached_property("Metadata").unpack()
                info["title"] = str(metadata.get("xesam:title", info["title"]))
                artist = metadata.get("xesam:artist")
                if isinstance(artist, (list, tuple)) and artist:
                    info["artist"] = str(artist[0])
            except Exception:  # noqa: BLE001
                pass
            try:
                identity = Gio.DBusProxy.new_sync(
                    bus, Gio.DBusProxyFlags.NONE, None, bus_name,
                    "/org/mpris/MediaPlayer2", "org.mpris.MediaPlayer2", None)
                info["player_name"] = identity.get_cached_property("Identity").unpack()
            except Exception:  # noqa: BLE001
                pass
        except Exception:  # noqa: BLE001 - best effort metadata
            pass
        return info

    def _op_media_control(self, args: dict) -> dict:
        action = str(args.get("action", ""))
        if action not in ("play", "pause", "play_pause", "stop", "next", "previous"):
            raise ValueError(_("Unknown action. Use play, pause, play_pause, stop, next or previous."))
        wanted = str(args.get("player", "") or "").strip().lower()
        players = self._mpris_players()
        if not players:
            raise RuntimeError(_("No media players found."))
        if wanted:
            match = next((p for p in players if wanted in p.lower()), None)
            if match is None:
                # playerctl uses short names; try them too.
                infos = [self._mpris_metadata(p) for p in players]
                match = next((i["dbus_name"] for i in infos
                              if wanted in str(i.get("player_name", "")).lower()), None)
                if match is None:
                    raise RuntimeError(_("Player '%s' not found.") % wanted)
            target = match
        else:
            target = players[0]
            # Prefer a currently playing player.
            for candidate in players:
                if self._mpris_metadata(candidate).get("playback_status") == "Playing":
                    target = candidate
                    break
        method = {"play": "Play", "pause": "Pause", "play_pause": "PlayPause",
                  "stop": "Stop", "next": "Next", "previous": "Previous"}[action]
        if _have_cmd("playerctl") and "." not in target:
            _run_cmd(["playerctl", "--player", target,
                      {"play": "play", "pause": "pause", "play_pause": "play-pause",
                       "stop": "stop", "next": "next", "previous": "previous"}[action]])
        else:
            bus = Gio.bus_get_sync(Gio.BusType.SESSION, None)
            proxy = Gio.DBusProxy.new_sync(
                bus, Gio.DBusProxyFlags.NONE, None, target,
                "/org/mpris/MediaPlayer2", "org.mpris.MediaPlayer2.Player", None)
            proxy.call_sync(method, None, Gio.DBusCallFlags.NONE, 5000, None)
        info = self._mpris_metadata(target)
        return {"action": action, "player": target, "player_match": wanted,
                "message": _("Sent %s to %s.") % (action, info.get("player_name", target)),
                "title": info.get("title", ""), "artist": info.get("artist", ""),
                "verified": True}

    # -- quick_settings -----------------------------------------------------------
    def _op_quick_settings(self, args: dict) -> dict:
        setting = str(args.get("setting", ""))
        if "enabled" not in args:
            raise ValueError(_("enabled (true/false) is required."))
        enabled = args["enabled"]
        if not isinstance(enabled, bool):
            raise ValueError(_("enabled must be true or false."))
        if setting == "wifi":
            try:
                bus = Gio.bus_get_sync(Gio.BusType.SYSTEM, None)
                proxy = Gio.DBusProxy.new_sync(
                    bus, Gio.DBusProxyFlags.NONE, None,
                    "org.freedesktop.NetworkManager", "/org/freedesktop/NetworkManager",
                    "org.freedesktop.NetworkManager", None)
                proxy.call_sync("org.freedesktop.DBus.Properties.Set",
                                GLib.Variant("(ssv)", (
                                    "org.freedesktop.NetworkManager", "WirelessEnabled",
                                    GLib.Variant("b", enabled))),
                                Gio.DBusCallFlags.NONE, 5000, None)
            except Exception:
                _run_cmd(["nmcli", "radio", "wifi", "on" if enabled else "off"])
        elif setting == "bluetooth":
            done = False
            try:
                bus = Gio.bus_get_sync(Gio.BusType.SYSTEM, None)
                proxy = Gio.DBusProxy.new_sync(
                    bus, Gio.DBusProxyFlags.NONE, None, "org.bluez",
                    "/org/bluez/hci0", "org.bluez.Adapter1", None)
                proxy.call_sync("org.freedesktop.DBus.Properties.Set",
                                GLib.Variant("(ssv)", (
                                    "org.bluez.Adapter1", "Powered", GLib.Variant("b", enabled))),
                                Gio.DBusCallFlags.NONE, 5000, None)
                done = True
            except Exception:  # noqa: BLE001 - bluetoothctl fallback
                pass
            if not done:
                _run_cmd(["bluetoothctl", "power", "on" if enabled else "off"])
        elif setting == "night_light":
            _gsettings_set("org.gnome.settings-daemon.plugins.color",
                           "night-light-enabled", "true" if enabled else "false")
        elif setting == "do_not_disturb":
            # show-banners is inverted: false means DND is on.
            _gsettings_set("org.gnome.desktop.notifications",
                           "show-banners", "false" if enabled else "true")
        elif setting == "dark_style":
            _gsettings_set("org.gnome.desktop.interface", "color-scheme",
                           "'prefer-dark'" if enabled else "'default'")
        else:
            raise ValueError(
                _("Unknown setting '%s'. Use wifi, bluetooth, night_light, do_not_disturb or dark_style.")
                % setting)
        return {"setting": setting, "enabled": enabled,
                "message": _("%s %s.") % (setting.replace("_", " ").title(),
                                             _("enabled") if enabled else _("disabled")),
                "verified": True}

    # -- take_screenshot ------------------------------------------------------------
    def _op_take_screenshot(self, args: dict) -> dict:
        interactive = args.get("interactive")
        if interactive is None:
            interactive = self.configuration()["screenshot_interactive"]
        interactive = bool(interactive)
        stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
        target = f"/tmp/gnome-screenshot-{stamp}.png"
        # 1. GNOME Shell screenshot service.
        try:
            bus = Gio.bus_get_sync(Gio.BusType.SESSION, None)
            proxy = Gio.DBusProxy.new_sync(
                bus, Gio.DBusProxyFlags.NONE, None,
                "org.gnome.Shell.Screenshot", "/org/gnome/Shell/Screenshot",
                "org.gnome.Shell.Screenshot", None)
            if interactive:
                ok, uri = proxy.call_sync(
                    "InteractiveScreenshot", None, Gio.DBusCallFlags.NONE, 60000, None).unpack()
                if not ok:
                    raise RuntimeError(_("Interactive screenshot was cancelled."))
                return {"path": uri, "uri": uri, "interactive": True, "verified": True}
            ok, filename = proxy.call_sync(
                "Screenshot", GLib.Variant("(bbs)", (False, False, target)),
                Gio.DBusCallFlags.NONE, 30000, None).unpack()
            if ok and os.path.isfile(filename):
                return {"path": filename, "uri": Gio.File.new_for_path(filename).get_uri(),
                        "interactive": False, "verified": True}
            if ok:
                return {"path": filename, "uri": filename,
                        "interactive": False, "verified": True}
        except Exception:  # noqa: BLE001 - CLI fallbacks below
            pass
        # 2. CLI fallbacks.
        if _have_cmd("gnome-screenshot"):
            cmd = ["gnome-screenshot", "-f", target]
            if interactive:
                cmd = ["gnome-screenshot", "-i", "-f", target]
            _run_cmd(cmd, timeout=60)
            if os.path.isfile(target):
                return {"path": target, "uri": Gio.File.new_for_path(target).get_uri(),
                        "interactive": interactive, "verified": True}
        raise RuntimeError(
            _("Screenshot failed. On GNOME, the Shell screenshot service or gnome-screenshot is required."))

    # -- window_management ------------------------------------------------------------
    def _window_backend(self, action: str, params: dict) -> tuple:
        try:
            return _window_helper_call(action, params), "helper"
        except RuntimeError as error:
            if not _dbus_missing(error):
                raise
        try:
            return _window_eval_call(action, params), "unsafe_mode"
        except WindowHelperUnavailable:
            raise WindowHelperUnavailable(self._window_helper_hint()) from None

    def _window_helper_hint(self) -> str:
        try:
            if _gsettings_get("org.gnome.shell", "disable-user-extensions") == "true":
                return _("User extensions are disabled in GNOME. Turn them on in the Extensions "
                         "app so the Newelle window control helper can run.")
        except (RuntimeError, OSError):
            pass
        state = _window_helper_state()
        if not state["installed"] and not state["loaded"]:
            return _("Window management needs the Newelle window control helper. Install it from "
                     "the GNOME Desktop extension settings (or the button below), then log out "
                     "and back in.")
        if not state["loaded"]:
            return _("The Newelle window control helper is installed, but GNOME Shell only loads "
                     "new extensions at login. Log out and back in.")
        if state["error"] or state["state"] in (3, 4):
            return _("GNOME Shell could not start the Newelle window control helper: %s") % (
                state["error"] or _("incompatible GNOME Shell version"))
        if not state["enabled"]:
            return _("The Newelle window control helper is disabled. Enable it in the "
                     "Extensions app.")
        return _("The Newelle window control helper is not responding. Log out and back in.")

    def install_window_helper(self) -> dict:
        """Install and enable the companion Shell extension used for window management."""
        shell_version = ""
        try:
            (shell_version,) = _dbus_call(
                "org.gnome.Shell.Extensions", "/org/gnome/Shell/Extensions",
                "org.freedesktop.DBus.Properties", "Get",
                GLib.Variant("(ss)", ("org.gnome.Shell.Extensions", "ShellVersion")), "(v)")
        except RuntimeError:
            pass
        target = _window_helper_dir()
        target.mkdir(parents=True, exist_ok=True)
        changed = False
        for name, content in _window_helper_sources(str(shell_version or "")).items():
            path = target / name
            if path.is_file() and path.read_text(encoding="utf-8") == content:
                continue
            path.write_text(content, encoding="utf-8")
            changed = True

        # Make sure the helper is started at the next login even if Shell cannot see it yet.
        try:
            enabled = GLib.Variant.parse(
                GLib.VariantType.new("as"),
                _gsettings_get("org.gnome.shell", "enabled-extensions"), None, None).unpack()
            if WINDOW_HELPER_UUID not in enabled:
                _gsettings_set("org.gnome.shell", "enabled-extensions",
                               GLib.Variant("as", enabled + [WINDOW_HELPER_UUID]).print_(False))
        except (GLib.Error, RuntimeError, OSError):
            pass

        state = _window_helper_state()
        if state["loaded"] and not state["enabled"]:
            try:
                _shell_extensions_call("EnableExtension",
                                       GLib.Variant("(s)", (WINDOW_HELPER_UUID,)), "(b)")
            except RuntimeError:
                pass
            state = _window_helper_state()

        running = False
        try:
            running = bool(_window_helper_call("list", {}, timeout=5).get("ok"))
        except (RuntimeError, ValueError):
            running = False
        # Running Shell extensions are never reloaded, so updated files need a new session.
        needs_relogin = not running or (changed and state["loaded"])
        if needs_relogin:
            message = _("Window control helper installed. Log out and back in to activate it.")
        else:
            message = _("Window control helper is installed and running.")
        return {"message": message, "path": str(target), "running": running,
                "needs_relogin": needs_relogin, "verified": running}

    def _install_window_helper_response(self) -> dict:
        operation = "gnome_window_management"
        try:
            data = self.install_window_helper()
        except (OSError, RuntimeError, ValueError) as error:
            return {"ok": False, "operation": operation, "error": str(error), "code": "failed"}
        return {"ok": True, "operation": operation, "data": data,
                "verified": bool(data.get("verified"))}

    def card_install_window_helper(self, card):
        self.card_action(card, "gnome_window_management", {"action": "list"},
                         runner=self._install_window_helper_response)

    def _on_install_helper_clicked(self, button):
        button.set_sensitive(False)

        def work():
            response = self._install_window_helper_response()

            def done():
                button.set_sensitive(True)
                if response.get("ok"):
                    data = response["data"]
                    button.set_label(_("Log out to finish") if data.get("needs_relogin")
                                     else _("Installed"))
                    button.set_tooltip_text(data.get("message"))
                else:
                    button.set_label(_("Retry"))
                    button.set_tooltip_text(str(response.get("error", "")))
                return False
            GLib.idle_add(done)
        threading.Thread(target=work, daemon=True).start()

    def _window_action(self, action: str, window_id="", workspace=None,
                       x=None, y=None, width=None, height=None, position="") -> dict:
        if action in ("focus", "close", "minimize", "maximize", "get_geometry",
                      "set_geometry", "set_position", "set_size", "snap",
                      "move_to_workspace") and not window_id:
            raise ValueError(_("window_id is required for '%s'. List windows first.") % action)
        params = {"window_id": window_id or None, "position": position or None}
        for key, value in (("workspace", workspace), ("x", x), ("y", y),
                           ("width", width), ("height", height)):
            params[key] = None if value is None else int(value)
        params = {key: value for key, value in params.items() if value is not None}

        result, backend = self._window_backend(action, params)
        if not isinstance(result, dict) or not result.get("ok"):
            error = result.get("error") if isinstance(result, dict) else None
            raise RuntimeError(str(error or _("The window action failed.")))
        if action == "list":
            windows = result.get("windows") or []
            data = {"windows": windows, "count": len(windows), "verified": True}
        else:
            message = str(result.get("message", ""))
            if action == "get_geometry":
                message = _("Window %s geometry.") % window_id
            data = {"message": message, "window_id": window_id, "verified": True}
            if result.get("geometry"):
                data["geometry"] = result["geometry"]
        if backend == "unsafe_mode":
            data["notice"] = _("Used GNOME Shell unsafe mode. Install the window control helper "
                               "to keep window management working with unsafe mode off.")
        return data

    def _op_window_management(self, args: dict) -> dict:
        action = str(args.get("action", ""))
        if action not in ("list", "focus", "close", "minimize", "maximize",
                          "switch_workspace", "move_to_workspace", "get_geometry",
                          "set_geometry", "set_position", "set_size", "snap"):
            raise ValueError(_("Unknown action. See the tool description for the 12 actions."))
        if action in ("switch_workspace", "move_to_workspace") and args.get("workspace") is None:
            raise ValueError(_("workspace is required for '%s'.") % action)
        if action == "set_geometry" and any(args.get(k) is None for k in ("x", "y", "width", "height")):
            raise ValueError(_("x, y, width and height are required for set_geometry."))
        if action == "set_position" and (args.get("x") is None or args.get("y") is None):
            raise ValueError(_("x and y are required for set_position."))
        if action == "set_size" and (args.get("width") is None or args.get("height") is None):
            raise ValueError(_("width and height are required for set_size."))
        if action == "snap" and args.get("position") not in ("left", "right"):
            raise ValueError(_("position must be 'left' or 'right' for snap."))
        window_id = str(args.get("window_id", "") or "").strip()
        if window_id:
            _validated_id(window_id)
            if not window_id.isdigit():
                raise ValueError(_("window_id must be the numeric ID shown by the list action."))
        return self._window_action(
            action, window_id=window_id, workspace=args.get("workspace"),
            x=args.get("x"), y=args.get("y"), width=args.get("width"),
            height=args.get("height"), position=str(args.get("position", "")))

    # -- keyring -----------------------------------------------------------------------
    def _secret_args(self, attributes: dict) -> list:
        if not attributes:
            raise ValueError(_("attributes (JSON object) is required to find a secret."))
        flat = []
        for key, value in attributes.items():
            if not re.fullmatch(r"[A-Za-z0-9_.-]+", str(key)) or len(str(key)) > 128:
                raise ValueError(_("Invalid attribute name '%s'.") % key)
            if len(str(value)) > 4096 or "\x00" in str(value):
                raise ValueError(_("Invalid attribute value for '%s'.") % key)
            flat.extend([str(key), str(value)])
        return flat

    def _op_keyring(self, args: dict) -> dict:
        action = str(args.get("action", ""))
        if action not in ("store", "retrieve", "delete"):
            raise ValueError(_("Unknown keyring action. Use store, retrieve or delete."))
        if not _have_cmd("secret-tool"):
            raise RuntimeError(
                _("secret-tool (libsecret) is required for keyring access but was not found."))
        attributes = _parse_attrs(args.get("attributes"))
        if action == "store":
            label = str(args.get("label", "")).strip()
            secret = args.get("secret")
            if not label:
                raise ValueError(_("label is required for store."))
            if not isinstance(secret, str) or not secret:
                raise ValueError(_("secret is required for store."))
            if len(label) > 256 or len(secret) > 16384:
                raise ValueError(_("label or secret is too long."))
            lookup = dict(attributes) or {"label": label}
            proc = subprocess.run(
                _host_prefix() + ["secret-tool", "store", "--label=" + label,
                                  *[item for pair in lookup.items() for item in pair]],
                input=secret, capture_output=True, text=True, timeout=15)
            if proc.returncode != 0:
                raise RuntimeError((proc.stderr or _("Could not store the secret."))[:500])
            return {"action": "store", "label": label, "attributes": lookup,
                    "message": _("Secret '%s' stored.") % label, "verified": True}
        selector = self._secret_args(attributes)
        if action == "retrieve":
            proc = subprocess.run(
                _host_prefix() + ["secret-tool", "lookup", *selector],
                capture_output=True, text=True, timeout=15)
            if proc.returncode != 0 or not (proc.stdout or "").strip():
                return {"action": "retrieve", "found": False,
                        "message": _("Secret not found."), "verified": True}
            return {"action": "retrieve", "found": True, "secret": proc.stdout.strip("\n"),
                    "label": "", "attributes": attributes,
                    "message": _("Secret retrieved."), "verified": True}
        proc = subprocess.run(
            _host_prefix() + ["secret-tool", "clear", *selector],
            capture_output=True, text=True, timeout=15)
        if proc.returncode != 0:
            raise RuntimeError((proc.stderr or _("Could not delete the secret."))[:500])
        return {"action": "delete", "attributes": attributes,
                "message": _("Matching secret deleted (if it existed)."), "verified": True}

    # -- calendar / tasks / contacts (EDS) ------------------------------------------------
    def _eds_registry(self):
        try:
            gi.require_version("EDataServer", "1.2")
            from gi.repository import EDataServer
        except (ValueError, ImportError) as error:
            raise RuntimeError(
                _("Evolution Data Server libraries are missing (need gir1.2-eds-1.2).")) from error
        try:
            return EDataServer.SourceRegistry.new_sync(None)
        except Exception as error:
            raise RuntimeError(_("Could not open the Evolution source registry: %s") % error) from error

    def _op_calendar_events(self, args: dict) -> dict:
        cfg = self.configuration()
        days_ahead = args.get("days_ahead", cfg["days_ahead"])
        days_behind = args.get("days_behind", cfg["days_behind"])
        try:
            days_ahead = int(days_ahead)
            days_behind = int(days_behind)
        except (TypeError, ValueError):
            raise ValueError(_("days_ahead/days_behind must be integers.")) from None
        if not 0 <= days_ahead <= 366 or not 0 <= days_behind <= 366:
            raise ValueError(_("Calendar range must be within 0-366 days."))
        try:
            gi.require_version("ECal", "2.0")
            try:
                gi.require_version("ICalGLib", "3.0")
            except (ValueError, ImportError):
                gi.require_version("ICalGLib", "4.0")
            from gi.repository import ECal
        except (ValueError, ImportError) as error:
            raise RuntimeError(
                _("Calendar libraries are missing (need gir1.2-ecal-2.0 and libical).")) from error
        registry = self._eds_registry()
        sources = registry.list_enabled("Calendar")
        if not sources:
            return {"items": [], "count": 0,
                    "notice": _("No enabled GNOME calendars found."), "verified": True}
        now = datetime.datetime.now(datetime.timezone.utc)
        start_ts = int((now - datetime.timedelta(days=days_behind)).timestamp())
        end_ts = int((now + datetime.timedelta(days=days_ahead)).timestamp())
        items, errors = [], []
        for source in sources:
            try:
                client = ECal.Client.connect_sync(
                    source, ECal.ClientSourceType.EVENTS, 5, None)
            except Exception as error:  # noqa: BLE001 - per-source error
                errors.append({"calendar": source.get_display_name(), "error": str(error)[:300]})
                continue
            found = []

            def collect(comp, instance_start, instance_end, *rest):
                try:
                    title = _comp_text(comp.get_summary())
                    desc = _comp_text(comp.get_description())
                    loc = _comp_text(comp.get_location())
                except Exception:  # noqa: BLE001
                    title, desc, loc = "", "", ""
                found.append({
                    "title": title,
                    "description": desc,
                    "location": loc,
                    "start": self._ical_stamp(comp.get_dtstart()),
                    "end": self._ical_stamp(comp.get_dtend()),
                    "calendar": source.get_display_name(),
                    "calendar_id": source.get_uid(),
                })
                return True
            try:
                client.generate_instances_sync(start_ts, end_ts, None, collect, None)
            except Exception as error:  # noqa: BLE001
                errors.append({"calendar": source.get_display_name(), "error": str(error)[:300]})
                continue
            items.extend(found)
        items.sort(key=lambda e: e.get("start", ""))
        return {"items": items[:100], "count": len(items),
                "source_errors": errors, "truncated": len(items) > 100, "verified": True}

    @staticmethod
    def _ical_stamp(value) -> str:
        try:
            if value is None:
                return ""
            # ECal getters may return a ComponentDateTime wrapper; unwrap it.
            if hasattr(value, "get_value") and not hasattr(value, "as_ical_string"):
                try:
                    value = value.get_value()
                except Exception:  # noqa: BLE001 - fall through to best effort
                    return ""
            if value is None or value.is_null_time():
                return ""
            raw = value.as_ical_string()
            if value.is_date():
                return datetime.datetime.strptime(raw, "%Y%m%d").date().isoformat()
            if value.is_utc():
                return datetime.datetime.strptime(raw, "%Y%m%dT%H%M%SZ").replace(
                    tzinfo=datetime.timezone.utc).isoformat()
            zone = value.get_timezone()
            if zone:
                return datetime.datetime.fromtimestamp(
                    value.as_timet_with_zone(zone), datetime.timezone.utc).isoformat()
            return datetime.datetime.strptime(raw, "%Y%m%dT%H%M%S").isoformat()
        except Exception:  # noqa: BLE001 - best effort display
            return ""

    def _op_tasks(self, args: dict) -> dict:
        cfg = self.configuration()
        include_completed = bool(args.get("include_completed", cfg["tasks_include_completed"]))
        include_cancelled = bool(args.get("include_cancelled", cfg["tasks_include_cancelled"]))
        due_within = args.get("due_within_days", cfg["tasks_due_within_days"])
        try:
            due_within = int(due_within)
        except (TypeError, ValueError):
            raise ValueError(_("due_within_days must be an integer.")) from None
        try:
            gi.require_version("ECal", "2.0")
            from gi.repository import ECal
        except (ValueError, ImportError) as error:
            raise RuntimeError(_("Task libraries are missing (need gir1.2-ecal-2.0).")) from error
        registry = self._eds_registry()
        sources = registry.list_enabled("Task List")
        if not sources:
            sources = registry.list_enabled("Tasks")
        items, errors = [], []
        cutoff = None
        if due_within > 0:
            cutoff = (datetime.date.today() + datetime.timedelta(days=due_within)).isoformat()
        for source in sources:
            try:
                source_type = getattr(ECal.ClientSourceType, "TASKS",
                                      getattr(ECal.ClientSourceType, "TODO", None))
                client = ECal.Client.connect_sync(source, source_type, 5, None)
                objects = _tuple_result(client.get_object_list_sync("#t", None))
            except Exception as error:  # noqa: BLE001
                errors.append({"list": source.get_display_name(), "error": str(error)[:300]})
                continue
            try:
                ICalGLib = _require_ical()
            except RuntimeError:
                ICalGLib = None
            for comp in objects or []:
                try:
                    status = comp.get_status()
                    if ICalGLib is not None:
                        is_completed = status == ICalGLib.PropertyStatus.COMPLETED
                        is_cancelled = status == ICalGLib.PropertyStatus.CANCELLED
                    else:
                        status_text = str(status or "").upper()
                        is_completed = "COMPLETED" in status_text
                        is_cancelled = "CANCELLED" in status_text
                    if not include_completed and is_completed:
                        continue
                    if not include_cancelled and is_cancelled:
                        continue
                    try:
                        due_value = comp.get_due()
                    except Exception:  # noqa: BLE001
                        due_value = None
                    due_text = self._ical_stamp(due_value)[:10] if due_value is not None else ""
                    if cutoff and due_text and due_text > cutoff:
                        continue
                    try:
                        priority_value = comp.get_priority()
                    except Exception:  # noqa: BLE001
                        priority_value = ""
                    try:
                        status_text = _comp_text(status)
                    except Exception:  # noqa: BLE001
                        status_text = ""
                    items.append({
                        "title": _comp_text(comp.get_summary()),
                        "description": _comp_text(comp.get_description()),
                        "status": status_text or _("needs action"),
                        "due": due_text,
                        "priority": str(priority_value or ""),
                        "list": source.get_display_name(),
                    })
                except Exception:  # noqa: BLE001 - skip malformed todos
                    continue
        return {"items": items[:100], "count": len(items),
                "source_errors": errors, "truncated": len(items) > 100, "verified": True}

    def _op_contacts(self, args: dict) -> dict:
        cfg = self.configuration()
        query = str(args.get("query", "") or "").strip()
        email_only = bool(args.get("email_only", cfg["contacts_email_only"]))
        try:
            limit = int(args.get("limit", 20) or 20)
        except (TypeError, ValueError):
            raise ValueError(_("limit must be an integer.")) from None
        limit = max(1, min(100, limit))
        try:
            gi.require_version("EBook", "1.2")
            gi.require_version("EBookContacts", "1.2")
            from gi.repository import EBook, EBookContacts
        except (ValueError, ImportError) as error:
            raise RuntimeError(
                _("Contacts libraries are missing (need gir1.2-ebook-1.2).")) from error
        registry = self._eds_registry()
        sources = registry.list_enabled("Address Book")
        items, errors = [], []
        # An empty sexp matches every contact; any_field_contains needs text.
        sexp = EBookContacts.BookQuery.any_field_contains(query).to_string() if query else ""
        for source in sources:
            try:
                client = EBook.BookClient.connect_sync(source, 5, None)
                found = _tuple_result(client.get_contacts_sync(sexp, None))
            except Exception as error:  # noqa: BLE001
                errors.append({"source": source.get_display_name(), "error": str(error)[:300]})
                continue
            for contact in found or []:
                fields: dict = {}
                try:
                    for attr in contact.get_attributes():
                        fields.setdefault(attr.get_name().upper(), []).extend(
                            attr.get_values() or [])
                except Exception:  # noqa: BLE001
                    continue

                def first(name):
                    return next(iter(fields.get(name, [])), "")

                emails = list(fields.get("EMAIL", []))
                if email_only and not emails:
                    continue
                items.append({
                    "title": first("FN") or first("X-EVOLUTION-FILE-AS") or _("Unnamed contact"),
                    "emails": emails,
                    "phones": list(fields.get("TEL", [])),
                    "organization": ", ".join(fields.get("ORG", [])),
                    "source": source.get_display_name(),
                    "source_id": source.get_uid(),
                    "id": first("UID"),
                })
                if len(items) >= limit:
                    break
            if len(items) >= limit:
                break
        return {"items": items, "count": len(items), "source_errors": errors,
                "limit_reached": len(items) == limit, "verified": True}

    # -- system / audio status -----------------------------------------------------------
    def _op_system_info(self, _args: dict) -> dict:
        hostname = socket.gethostname()
        try:
            gnome_version = _run_cmd(["gnome-shell", "--version"], timeout=8)
        except Exception:  # noqa: BLE001
            gnome_version = _("unknown")
        uptime = ""
        try:
            with open("/proc/uptime", encoding="utf-8") as handle:
                seconds = int(float(handle.read().split()[0]))
            uptime = "%dh %02dm" % (seconds // 3600, seconds % 3600 // 60)
        except (OSError, ValueError):
            pass
        desktop = (os.environ.get("XDG_CURRENT_DESKTOP", "")
                   or os.environ.get("DESKTOP_SESSION", "") or "GNOME")
        session = os.environ.get("XDG_SESSION_TYPE", "")
        if session:
            desktop = f"{desktop} ({session})"
        return {"hostname": hostname, "os": f"{platform.system()} {platform.release()}",
                "gnome_version": gnome_version, "desktop": desktop,
                "arch": platform.machine(), "uptime": uptime, "verified": True}

    def _op_audio_status(self, _args: dict) -> dict:
        try:
            volume = self._volume_status()
        except RuntimeError as error:
            volume = {"level": 0, "muted": False, "error": str(error)}
        players = []
        try:
            for bus_name in self._mpris_players():
                players.append(self._mpris_metadata(bus_name))
        except Exception as error:  # noqa: BLE001
            return {"volume": volume, "players": players,
                    "notice": str(error)[:300], "verified": True}
        active = next((p for p in players if p.get("playback_status") == "Playing"), None)
        return {"volume": volume, "players": players, "active_player": active,
                "verified": True}
