# transit-tray

*Public transport departures from home in the Linux panel and a route planner with a map. Austria uses the operators' own interfaces; the rest of Europe uses [Transitous](https://transitous.org). UI in English, documentation in German.*

Ein Statusleisten-Widget für Linux (gebaut für COSMIC auf Pop!_OS, läuft überall mit Statusleisten-Symbolen nach StatusNotifierItem): oben rechts das Haltestellen-H, im Menü die nächsten Abfahrten an den Haltestellen bei dir zuhause, dazu ein Fenster mit Routenplaner und Karte.

## Was es kann

- **Menü:** je gewählter Haltestelle die nächsten Abfahrten mit Uhrzeit, Linie, Richtung und Verspätung. Was du zu Fuß nicht mehr erreichst, fällt weg.
- **Filter je Haltestelle:** welche Linien und Richtungen Menü und Abfahrten zeigen. Richtungen gelten, wie der Betreiber sie führt (Hin- und Rückrichtung, mit Kurzführungen), bei Zügen je Ziel; neue Linien und Ziele erscheinen, bis man sie abhakt.
- **Routenplaner:** Öffis, Rad + Öffis, Rad, zu Fuß und Auto auf einmal. Der Verlauf zeigt jede Etappe mit Steig, Umstiege mit Fußweg und Wartezeit (auch innerhalb einer Station, etwa „stairs up“), und die Strecke auf der Karte. Wo der Planer keine Echtzeit hat (etwa die U-Bahn), holt das Widget sie beim Betreiber nach und rechnet eine Verspätung bis zur Ankunft weiter.
- **Nur sinnvolle Verbindungen:** Eine Verbindung fällt weg, wenn eine andere nicht früher losgeht, höchstens 3 Minuten später ankommt (5, wenn man dafür 10 Minuten später losgeht) und klar weniger Aufwand ist – Dauer plus 5 Minuten je Umstieg plus die Hälfte von Fußweg und Rad. Weg sind damit etwa „20 Minuten früher los für 3 Minuten früher da“ oder 25 Minuten Fußweg statt der Bim. Eine frühere Verbindung verdrängt nie eine spätere: Wer sie knapp verpasst, sieht die nächste gute. Ist man zu Fuß fast gleich schnell, steht das statt der Liste.
- **Rad + Öffis (Bike & Ride):** mit dem eigenen Rad zur Haltestelle, dort parken, weiter mit Öffis. Gezeigt nur, wenn es mindestens 5 Minuten (bzw. 15 %) schneller ist als nur Öffis und als die ganze Strecke mit dem Rad; sonst sagt die Liste, was schneller ist.
- **Autorouten zur Wahl:** die schnellste und bis zu zwei Alternativen, die höchstens 5 Minuten (bzw. 15 %) langsamer sind und großteils andere Straßen nehmen, jeweils mit „via“ und den anderen grau auf der Karte.
- **Abfahrten:** der Fahrtverlauf jeder Abfahrt mit allen Halten. Welche Haltestelle zuerst kommt, legen Pfeile neben ihrem Namen fest – unter „Departures“ und in „Home & stops“.
- **Live-Verkehr** für Autorouten mit einem eigenen, kostenlosen TomTom-Schlüssel (optional).
- **Europaweit:** Zuhause, Start und Ziel können überall in Europa liegen; Uhrzeiten stehen in der Ortszeit.

## Woher die Daten kommen

| Bereich | Quelle |
|---|---|
| Wien (U-Bahn, Bim, Bus) | Wiener Linien: Open Data (Abfahrten, Echtzeit). Verbindungen rechnet die Verkehrsauskunft Österreich über VOR AnachB – mit ihr rechnet auch die WienMobil-App der Wiener Linien. Der Open-Data-Routenplaner der Wiener Linien fährt nach altem Fahrplan (im Oktober 2026 ohne die bis zum Stadion verlängerte 18). |
| Linz (Bim, Bus, Pöstlingbergbahn) | Linz AG Fahrplanauskunft (EFA) |
| Züge, S-Bahn, Postbus, sonst Österreich | ÖBB-Fahrplanauskunft (HAFAS) |
| private Regionalbusse in Ostösterreich / Oberösterreich | VOR AnachB bzw. OÖVV (Verkehrsauskunft Österreich) |
| Rest Europas und über die Grenze, Rad + Öffis überall | [Transitous](https://transitous.org): offene Fahrplandaten der Betreiber, Echtzeit wo vorhanden ([Quellen](https://transitous.org/sources/)) |
| Rad, zu Fuß, Auto | TomTom (mit Schlüssel, mit Verkehr), sonst die OSRM-Router der FOSSGIS auf OpenStreetMap |
| Karte | [basemap.at](https://basemap.at) in Österreich (CC BY 4.0), rundherum © [OpenStreetMap](https://www.openstreetmap.org/copyright)-Mitwirkende, an der Grenze weich ineinander übergehend |

Nur die Schnittstelle der Wiener Linien ist offiziell dokumentiert. Die von ÖBB, VOR, OÖVV und Linz AG sind die ihrer Apps und Webseiten und können sich ändern; dann rechnet für eine Weile die ÖBB-Auskunft bzw. fehlen Abfahrten (der Grund steht im Journal).

## Installieren

Voraussetzungen (Debian, Ubuntu, Pop!_OS):

```sh
sudo apt install python3-gi python3-gi-cairo gir1.2-gtk-3.0 gir1.2-ayatanaappindicator3-0.1
```

Optional `python3-numpy`: Damit läuft basemap.at an der Grenze weich in OpenStreetMap aus (ohne seinen lila Grenzsaum); ohne numpy wechselt die Karte dort hart.

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
- Jede Anfrage trägt den User-Agent `transit-tray/3.2 (+https://github.com/magnusgoeppel/transit-tray)`. Transitous und die OpenStreetMap-Kacheln verlangen Name, Version und Kontakt. Wer eine geänderte Fassung weitergibt, trägt dort (`APP_URL` im Skript) die eigene Adresse ein.

## Rücksicht auf die Dienste

- **Transitous** wird von Freiwilligen betrieben und ist nur für offene, nicht kommerzielle Projekte gedacht ([Bedingungen](https://transitous.org/api/)). Das Widget fragt Abfahrten dort höchstens alle 4 Minuten ab – dazu einmal, wenn man den Filter einer Haltestelle öffnet oder ändert –, rechnet Rad + Öffis mit einer Anfrage je Routensuche (nicht unter 1,5 km) und nennt die Quellen im Verlauf („Route by Transitous“).
- **OpenStreetMap-Kacheln** nach der [Tile Usage Policy](https://operations.osmfoundation.org/policies/tiles/): nur außerhalb Österreichs und an der Grenze, 30 Tage zwischengespeichert.
- Abfahrten insgesamt alle 2 Minuten, über getaktete Verbindungen alle 5, nachts ohne Fahrten alle 15.

## Lizenz

MIT, siehe [LICENSE](LICENSE).
