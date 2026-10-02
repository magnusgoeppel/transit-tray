#!/usr/bin/env bash
# transit-tray fuer den aktuellen Benutzer installieren (ohne root): Skript nach
# ~/.local/bin, "Transit" in den App-Starter, Start mit der Anmeldung.
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
bin="$HOME/.local/bin/transit-tray.py"
install -Dm755 "$src/transit-tray.py" "$bin"
install -d "$HOME/.local/share/applications" "$HOME/.config/autostart"
sed "s|@SCRIPT@|$bin|g" "$src/desktop/transit-tray.desktop" >"$HOME/.local/share/applications/transit-tray.desktop"
sed "s|@SCRIPT@|$bin|g" "$src/desktop/transit-tray-autostart.desktop" >"$HOME/.config/autostart/transit-tray.desktop"
echo "Installiert. Jetzt starten mit:  python3 $bin &"
echo "Ab der naechsten Anmeldung startet es von selbst."
