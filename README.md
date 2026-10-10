# transit-tray

*Public transport departures from home in the Linux panel and a route planner with a map. Austria uses the operators' own interfaces; the rest of Europe uses [Transitous](https://transitous.org). UI in English, documentation in German.*

Ein Statusleisten-Widget für Linux (gebaut für COSMIC auf Pop!_OS, läuft überall mit Statusleisten-Symbolen nach StatusNotifierItem): oben rechts das Haltestellen-H, im Menü die nächsten Abfahrten an den Haltestellen bei dir zuhause, dazu ein Fenster mit Routenplaner und Karte.

## Was es kann

- **Menü:** je gewählter Haltestelle die nächsten Abfahrten mit Uhrzeit, Linie, Richtung und Verspätung. Was du zu Fuß nicht mehr erreichst, fällt weg.
- **Filter je Haltestelle:** welche Linien und Richtungen Menü und Abfahrten zeigen. Richtungen gelten, wie der Betreiber sie führt (Hin- und Rückrichtung, mit Kurzführungen), bei Zügen je Ziel; neue Linien und Ziele erscheinen, bis man sie abhakt.
- **Routenplaner:** Öffis, Rad, zu Fuß und Auto auf einmal. Der Verlauf zeigt jede Etappe mit Steig, Umstiege mit Fußweg und Wartezeit (auch innerhalb einer Station, etwa „stairs up“), und die Strecke auf der Karte.
- **Abfahrten:** der Fahrtverlauf jeder Abfahrt mit allen Halten. Welche Haltestelle zuerst kommt, legen Pfeile neben ihrem Namen fest – unter „Departures“ und in „Home & stops“.
- **Live-Verkehr** für Autorouten mit einem eigenen, kostenlosen TomTom-Schlüssel (optional).
- **Europaweit:** Zuhause, Start und Ziel können überall in Europa liegen; Uhrzeiten stehen in der Ortszeit.

## Woher die Daten kommen

| Bereich | Quelle |
|---|---|
| Wien (U-Bahn, Bim, Bus) | Wiener Linien: Open Data (Echtzeit) und Routenplaner (EFA) |
| Linz (Bim, Bus, Pöstlingbergbahn) | Linz AG Fahrplanauskunft (EFA) |
| Züge, S-Bahn, Postbus, sonst Österreich | ÖBB-Fahrplanauskunft (HAFAS) |
| private Regionalbusse in Ostösterreich / Oberösterreich | VOR AnachB bzw. OÖVV (Verkehrsauskunft Österreich) |
| Rest Europas und über die Grenze | [Transitous](https://transitous.org): offene Fahrplandaten der Betreiber, Echtzeit wo vorhanden ([Quellen](https://transitous.org/sources/)) |
| Rad, zu Fuß, Auto | TomTom (mit Schlüssel, mit Verkehr), sonst die OSRM-Router der FOSSGIS auf OpenStreetMap |
| Karte | [basemap.at](https://basemap.at) in Österreich (CC BY 4.0), rundherum © [OpenStreetMap](https://www.openstreetmap.org/copyright)-Mitwirkende |

Nur die Schnittstelle der Wiener Linien ist offiziell dokumentiert. Die von ÖBB, VOR, OÖVV und Linz AG sind die ihrer Apps und Webseiten und können sich ändern; dann rechnet für eine Weile die ÖBB-Auskunft bzw. fehlen Abfahrten (der Grund steht im Journal).

## Installieren

Voraussetzungen (Debian, Ubuntu, Pop!_OS):

```sh
sudo apt install python3-gi python3-gi-cairo gir1.2-gtk-3.0 gir1.2-ayatanaappindicator3-0.1
```

Dann:

```sh
git clone https://github.com/magnusgoeppel/transit-tray
cd transit-tray
./install.sh
python3 ~/.local/bin/transit-tray.py &
```

`install.sh` legt das Skript nach `~/.local/bin`, „Transit“ in den App-Starter und einen Autostart-Eintrag an. Beim ersten Start öffnet sich „Home & stops“: Adresse suchen, Haltestellen in der Nähe abhaken, mit den Pfeilen ordnen und über den Trichter ihre Linien und Richtungen wählen.

## Befehle

```sh
python3 ~/.local/bin/transit-tray.py            # Symbol in der Statusleiste
python3 ~/.local/bin/transit-tray.py --route    # Routenplaner öffnen
python3 ~/.local/bin/transit-tray.py --home     # Zuhause, Haltestellen, TomTom
python3 ~/.local/bin/transit-tray.py --once     # einmal abfragen, Menü als Text
```

## Daten und Datenschutz

- Zuhause, Haltestellen, ihre Filter, letzte Ziele und der TomTom-Schlüssel stehen nur lokal in `~/.config/transit-tray/settings.json` (nur für dich lesbar), Kartenkacheln und der letzte Stand in `~/.cache/transit-tray`. Im Fenster steht der Schlüssel verdeckt; das Auge im Feld zeigt ihn.
- Abfragen gehen direkt an die Dienste oben; für Routen mit den Koordinaten von Start und Ziel.
- Jede Anfrage trägt den User-Agent `transit-tray/3.1 (+https://github.com/magnusgoeppel/transit-tray)`. Transitous und die OpenStreetMap-Kacheln verlangen Name, Version und Kontakt. Wer eine geänderte Fassung weitergibt, trägt dort (`APP_URL` im Skript) die eigene Adresse ein.

## Rücksicht auf die Dienste

- **Transitous** wird von Freiwilligen betrieben und ist nur für offene, nicht kommerzielle Projekte gedacht ([Bedingungen](https://transitous.org/api/)). Das Widget fragt Abfahrten dort höchstens alle 4 Minuten ab – dazu einmal, wenn man den Filter einer Haltestelle öffnet oder ändert – und nennt die Quellen im Verlauf („Route by Transitous“).
- **OpenStreetMap-Kacheln** nach der [Tile Usage Policy](https://operations.osmfoundation.org/policies/tiles/): nur außerhalb Österreichs, 30 Tage zwischengespeichert.
- Abfahrten insgesamt alle 2 Minuten, über getaktete Verbindungen alle 5, nachts ohne Fahrten alle 15.

## Lizenz

MIT, siehe [LICENSE](LICENSE).
