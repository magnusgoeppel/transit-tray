#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
transit-tray - die naechsten Abfahrten bei dir zuhause oben rechts in der
COSMIC-Statusleiste, dazu ein Routenplaner mit Karte fuer Oeffis, Rad, zu Fuss und
Auto. Im Stil der anderen Widgets (weather-tray.py, pomodoro-tray.py).

Das Symbol ist das Haltestellen-H. Das Menue zeigt fuer die Haltestellen bei dir die
naechsten Abfahrten mit Uhrzeit und Verspaetung; was man zu Fuss nicht mehr
erreicht, faellt weg. Ein Klick auf eine Abfahrt zeigt ihren Fahrtverlauf, "Plan a
route..." oeffnet den Routenplaner (gespeicherte und letzte Ziele zur Wahl, der Stern
speichert ein Ziel), "Home & stops..." die Wahl von Zuhause, der Haltestellen
(Reihenfolge; welche Linien und Richtungen sie zeigen) und den TomTom-Schluessel.

In Oesterreich kommt jedes Verkehrsmittel von der Schnittstelle seines Betreibers:
Wiener Linien (Open Data), Linz AG (EFA), ÖBB (Zuege, Postbus), VOR und OÖVV
(Verkehrsauskunft Oesterreich, private Regionalbusse). Verbindungen in Wien rechnet wie
in der WienMobil-App der Wiener Linien die Verkehrsauskunft Oesterreich. Im Rest
Europas (und ueber die Grenze) rechnet Transitous mit den offenen Fahrplaenen der
Betreiber. Auto, Rad und zu Fuss rechnet TomTom mit aktuellem Verkehr (kostenloser
Schluessel), ohne Schluessel die OpenStreetMap-Router der FOSSGIS. Die Karte ist in
Oesterreich basemap.at, rundherum OpenStreetMap, an der Grenze weich ineinander
uebergehend.

Quellcode: https://github.com/magnusgoeppel/transit-tray (MIT-Lizenz).

  python3 transit-tray.py              Tray-Symbol starten
  python3 transit-tray.py --route      Routenplaner oeffnen (startet das Widget bei Bedarf)
  python3 transit-tray.py --home       Zuhause, Haltestellen, TomTom (ebenso)
  python3 transit-tray.py --once       einmal abfragen, Menuezeilen ausgeben, beenden
                                       (Exit-Code 0 ok, 2 kein Zuhause, 3 offline,
                                       4 unerwartete Antwort)

TRANSIT_TRAY_HAFAS, TRANSIT_TRAY_OSRM und TRANSIT_TRAY_MOTIS ersetzen die Adressen von
ÖBB, OSRM und Transitous (zum Testen).
"""

import argparse
import collections
import concurrent.futures
import datetime as dt
import fcntl
import gzip
import http.client
import json
import math
import os
import re
import signal
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import zoneinfo

# ------------------------------------------------------------------ Schnittstellen

# HAFAS (HCI): die ÖBB-Auskunft (wie in der ÖBB-App) und die Verkehrsauskunft
# Oesterreich (VAO) von VOR (AnachB) und OÖVV. Keine dokumentierten Schnittstellen -
# die Zugangsdaten sind die der jeweiligen App bzw. Webseite.
_VAO = {"lang": "deu", "ver": "1.59", "ext": "VAO.22", "auth": {"type": "AID", "aid": "wf7mcf9bv3nv8g5f"}}
HAFAS_SOURCES = {
    "oebb": {"url": os.environ.get("TRANSIT_TRAY_HAFAS", "https://fahrplan.oebb.at/bin/mgate.exe"),
             "base": {"lang": "de", "ver": "1.57", "auth": {"type": "AID", "aid": "OWDL4fE4ixNiPBBm"},
                      "client": {"id": "OEBB", "v": "6030600", "type": "IPH", "name": "oebbPROD-ADHOC"}}},
    "vor": {"url": "https://anachb.vor.at/hamm/gate",
            "base": dict(_VAO, client={"id": "VAO", "type": "WEB", "name": "webapp", "l": "vs_anachb", "v": 10022})},
    "ooevv": {"url": "https://verkehrsauskunft.ooevv.at/hamm/gate",
              "base": dict(_VAO, client={"id": "VAO", "type": "WEB", "name": "webapp", "l": "vs_ooevv", "v": 10022})},
}
# EFA (Mentz): die Fahrplanauskunft der Linz AG und der Open-Data-Routenplaner der Wiener
# Linien - von ihm nur die Haltestellen, Verbindungen siehe CITY_PLANNERS. Echtzeit-
# Abfahrten der Wiener Linien kommen aus ihrer Open-Data-Schnittstelle.
EFA_SOURCES = {"wl": "https://www.wienerlinien.at/ogd_routing", "linzag": "https://www.linzag.at/static"}
WL_MONITOR = "https://www.wienerlinien.at/ogd_realtime/monitor"
# Ausserhalb Oesterreichs: Transitous (MOTIS 2), von Freiwilligen betrieben, mit den
# offenen Fahrplaenen (GTFS, Echtzeit wo vorhanden) der Betreiber in ganz Europa.
# Bedingungen: offener Code, nicht kommerziell, Kontakt im User-Agent, Quellen verlinkt.
MOTIS_URL = os.environ.get("TRANSIT_TRAY_MOTIS", "https://api.transitous.org/api")
TRANSITOUS_SOURCES = "https://transitous.org/sources/"
SOURCE_NAMES = {"oebb": "ÖBB", "vor": "VOR", "ooevv": "OÖVV", "wl": "Wiener Linien", "linzag": "Linz AG",
                "motis": "Transitous", "tomtom": "TomTom", "osrm": "OpenStreetMap"}
# Wo welche Schnittstelle zustaendig ist (grob, lon/lat-Rechtecke): Stadtgebiete fuer
# Wiener Linien und Linz AG, Bundeslaender fuer die Verbuende.
CITY_AREAS = {"wl": (16.18, 48.11, 16.58, 48.33), "linzag": (14.17, 48.21, 14.40, 48.38)}
VERBUND_AREAS = {"ooevv": (12.75, 47.45, 14.60, 48.78), "vor": (14.45, 46.85, 17.17, 49.03)}
# Wer Verbindungen innerhalb der Stadt rechnet: in Linz die Linz AG, in Wien die VAO (ueber
# AnachB des VOR) - mit ihr rechnet auch die WienMobil-App der Wiener Linien. Deren
# Open-Data-Routenplaner faehrt nach altem Fahrplan: Im Oktober 2026 kannte er die seit
# September bis zum Stadion verlaengerte 18 und den neuen 78A nicht und schickte deshalb
# auf Umwege mit einer Viertelstunde mehr.
CITY_PLANNERS = {"wl": "vor", "linzag": "linzag"}
# Oesterreichs Grenze (OpenStreetMap ueber Nominatim, auf rund 1 km vereinfacht), lon,lat:
# entscheidet, wessen Fahrplaene gelten (Betreiber in Oesterreich oder Transitous) und
# wo basemap.at die Karte hat. Der zweite Ring ist Jungholz.
AUSTRIA_BORDER = (
    ("10.454,47.556 10.431,47.504 10.468,47.477 10.476,47.432 10.437,47.413 10.437,47.380 "
     "10.395,47.376 10.330,47.305 10.232,47.271 10.172,47.279 10.216,47.311 10.200,47.326 "
     "10.236,47.382 10.182,47.392 10.166,47.369 10.119,47.376 10.100,47.355 10.069,47.410 "
     "10.106,47.429 10.092,47.459 10.070,47.456 10.045,47.488 10.001,47.482 9.965,47.521 9.971,47.546 "
     "9.922,47.530 9.881,47.548 9.875,47.529 9.816,47.548 9.827,47.580 9.800,47.596 9.766,47.589 "
     "9.735,47.534 9.680,47.523 9.559,47.542 9.562,47.496 9.595,47.463 9.659,47.452 9.644,47.434 "
     "9.674,47.390 9.605,47.351 9.531,47.271 9.567,47.242 9.552,47.224 9.585,47.205 9.565,47.170 "
     "9.622,47.151 9.635,47.128 9.621,47.111 9.634,47.083 9.607,47.061 9.682,47.062 9.836,47.013 "
     "9.877,47.021 9.892,46.990 9.871,46.963 9.876,46.935 10.018,46.902 10.105,46.841 10.233,46.866 "
     "10.241,46.931 10.316,46.925 10.308,46.947 10.347,46.990 10.389,47.001 10.427,46.976 "
     "10.424,46.959 10.489,46.938 10.470,46.855 10.555,46.849 10.546,46.837 10.667,46.875 "
     "10.764,46.823 10.730,46.788 10.786,46.796 10.883,46.763 11.025,46.766 11.039,46.805 "
     "11.083,46.822 11.071,46.853 11.102,46.890 11.096,46.912 11.164,46.940 11.164,46.966 "
     "11.320,46.992 11.406,46.965 11.479,47.011 11.539,46.984 11.627,47.013 11.747,46.969 "
     "11.917,47.033 12.186,47.092 12.241,47.069 12.205,47.027 12.121,47.007 12.132,46.962 "
     "12.169,46.937 12.144,46.914 12.190,46.906 12.215,46.874 12.274,46.884 12.307,46.841 "
     "12.283,46.815 12.284,46.783 12.357,46.775 12.384,46.716 12.561,46.653 12.691,46.657 "
     "12.731,46.634 12.776,46.647 12.831,46.631 12.853,46.605 13.086,46.602 13.169,46.589 "
     "13.240,46.552 13.321,46.551 13.372,46.579 13.794,46.505 13.912,46.521 14.006,46.481 "
     "14.051,46.493 14.122,46.477 14.163,46.434 14.430,46.447 14.443,46.423 14.479,46.414 "
     "14.522,46.427 14.564,46.372 14.596,46.437 14.699,46.464 14.715,46.500 14.819,46.509 "
     "14.823,46.546 14.870,46.607 14.920,46.602 14.923,46.621 14.956,46.633 14.979,46.601 "
     "15.041,46.652 15.145,46.660 15.236,46.639 15.414,46.656 15.457,46.639 15.462,46.615 "
     "15.502,46.614 15.550,46.638 15.544,46.669 15.595,46.690 15.630,46.680 15.650,46.706 "
     "15.768,46.699 15.840,46.722 16.038,46.656 16.030,46.712 16.004,46.717 15.985,46.752 "
     "15.991,46.833 16.058,46.839 16.133,46.876 16.200,46.942 16.276,46.963 16.290,47.014 "
     "16.303,46.998 16.512,47.002 16.439,47.030 16.521,47.056 16.473,47.074 16.463,47.095 "
     "16.529,47.127 16.517,47.149 16.454,47.142 16.455,47.187 16.419,47.195 16.443,47.234 "
     "16.432,47.253 16.467,47.253 16.489,47.280 16.465,47.334 16.434,47.353 16.461,47.383 "
     "16.445,47.407 16.485,47.409 16.497,47.389 16.517,47.411 16.576,47.406 16.662,47.456 "
     "16.670,47.474 16.652,47.500 16.715,47.540 16.665,47.566 16.673,47.605 16.652,47.623 "
     "16.573,47.620 16.422,47.665 16.447,47.696 16.475,47.681 16.541,47.712 16.548,47.752 "
     "16.609,47.760 16.721,47.735 16.749,47.681 16.828,47.683 16.867,47.722 16.875,47.688 "
     "17.093,47.708 17.051,47.794 17.074,47.808 17.010,47.858 17.085,47.874 17.113,47.927 "
     "17.091,47.934 17.117,47.961 17.095,47.971 17.161,48.007 17.067,48.031 17.088,48.046 "
     "17.068,48.055 17.093,48.100 17.057,48.144 17.026,48.141 16.976,48.172 16.946,48.236 "
     "16.957,48.264 16.908,48.288 16.895,48.311 16.909,48.326 16.843,48.352 16.833,48.381 "
     "16.850,48.383 16.864,48.419 16.850,48.449 16.954,48.543 16.902,48.718 16.800,48.706 "
     "16.725,48.738 16.683,48.728 16.664,48.781 16.594,48.783 16.541,48.814 16.519,48.798 "
     "16.460,48.809 16.435,48.766 16.378,48.728 16.343,48.746 16.330,48.731 16.094,48.747 "
     "15.994,48.779 15.950,48.805 15.958,48.823 15.893,48.835 15.898,48.848 15.843,48.860 "
     "15.842,48.877 15.780,48.875 15.754,48.852 15.690,48.856 15.612,48.898 15.513,48.914 "
     "15.468,48.952 15.279,48.995 15.262,48.954 15.160,48.942 15.156,48.993 15.021,49.021 "
     "14.990,49.010 14.998,48.992 14.976,48.971 14.993,48.904 14.973,48.875 14.985,48.842 "
     "14.953,48.790 14.980,48.772 14.956,48.758 14.809,48.779 14.808,48.734 14.727,48.687 "
     "14.712,48.650 14.721,48.602 14.702,48.583 14.663,48.582 14.610,48.628 14.562,48.603 "
     "14.503,48.617 14.470,48.648 14.444,48.643 14.456,48.625 14.431,48.589 14.386,48.593 "
     "14.388,48.572 14.358,48.575 14.333,48.552 14.272,48.581 14.067,48.595 14.042,48.613 "
     "14.048,48.627 14.011,48.640 14.054,48.653 14.059,48.674 13.843,48.773 13.795,48.715 "
     "13.837,48.701 13.814,48.692 13.826,48.619 13.801,48.574 13.770,48.554 13.754,48.564 "
     "13.731,48.515 13.509,48.591 13.475,48.556 13.438,48.557 13.458,48.512 13.427,48.457 "
     "13.439,48.431 13.411,48.375 13.330,48.324 13.256,48.294 13.181,48.295 13.022,48.258 "
     "12.956,48.209 12.870,48.201 12.787,48.124 12.759,48.127 12.759,48.075 12.850,48.016 "
     "12.874,47.964 12.938,47.943 13.004,47.849 12.905,47.723 12.974,47.707 13.018,47.723 "
     "13.081,47.687 13.099,47.635 13.063,47.601 13.071,47.587 13.044,47.583 13.057,47.562 "
     "13.031,47.533 13.048,47.492 13.004,47.463 12.794,47.557 12.779,47.579 12.824,47.612 "
     "12.759,47.652 12.781,47.674 12.607,47.674 12.575,47.632 12.499,47.625 12.441,47.674 "
     "12.440,47.695 12.255,47.679 12.241,47.694 12.257,47.743 12.162,47.701 12.204,47.607 "
     "12.022,47.611 12.009,47.625 11.855,47.602 11.844,47.581 11.636,47.595 11.606,47.581 "
     "11.572,47.515 11.442,47.518 11.384,47.472 11.421,47.445 11.339,47.450 11.270,47.398 "
     "11.225,47.395 11.253,47.428 11.207,47.434 11.115,47.395 10.972,47.400 10.984,47.430 "
     "10.930,47.470 10.937,47.481 10.870,47.483 10.872,47.500 10.918,47.514 10.890,47.537 "
     "10.778,47.514 10.691,47.559 10.598,47.570 10.571,47.533"),
    "10.454,47.556 10.471,47.580 10.482,47.584 10.429,47.578",
)

# Rad, zu Fuss, Auto: TomTom mit aktuellem Verkehr, wenn ein Schluessel eingetragen ist,
# sonst die freien OSRM-Router der FOSSGIS auf OpenStreetMap-Daten (ohne Verkehr).
TOMTOM_ROUTE = "https://api.tomtom.com/routing/1/calculateRoute/%s/json"
TOMTOM_FLOW = "https://api.tomtom.com/traffic/map/4/tile/flow/relative0/{z}/{x}/{y}.png?key={key}&tileSize=512"
TOMTOM_SIGNUP = "https://developer.tomtom.com/user/register"
TOMTOM_MODES = {"car": "car", "bike": "bicycle", "walk": "pedestrian"}
OSRM_URL = os.environ.get("TRANSIT_TRAY_OSRM", "https://routing.openstreetmap.de")
OSRM_PROFILES = {"bike": "bike", "walk": "foot", "car": "car"}
MAP_URL = "https://www.openstreetmap.org/directions?engine=fossgis_osrm_%s&route=%.5f%%2C%.5f%%3B%.5f%%2C%.5f"
# Die Karte: basemap.at Standard (Grundkarte der Bundeslaender, CC BY 4.0) in
# Oesterreich. Ausserhalb sind ihre Kacheln durchsichtig, darunter liegt OpenStreetMap
# (Kacheln der OSMF: mit Kennung im User-Agent und Cache erlaubt). Auf Bildschirmen
# mit Skalierung ab 125 % die HiDPI-Kacheln von basemap.at (512 px, nur JPEG - an der
# Grenze daher die durchsichtigen normalen).
TILE_URLS = {"normal": ("https://mapsneu.wien.gv.at/basemap/geolandbasemap/normal/google3857/{z}/{y}/{x}.png", 256),
             "hidpi": ("https://mapsneu.wien.gv.at/basemap/bmaphidpi/normal/google3857/{z}/{y}/{x}.jpeg", 512),
             "osm": ("https://tile.openstreetmap.org/{z}/{x}/{y}.png", 256)}
MAP_CREDITS = {"basemap": "basemap.at", "osm": "© OpenStreetMap contributors"}

APP_URL = "https://github.com/magnusgoeppel/transit-tray"
# Transitous und die OpenStreetMap-Kacheln verlangen Name, Version und Kontakt
HEADERS = {"Accept": "application/json", "Accept-Encoding": "gzip", "User-Agent": "transit-tray/3.3 (+%s)" % APP_URL}
TIMEOUT = 20

# Abfragen
POLL = 2 * 60           # Abfahrten neu holen
POLL_METERED = 5 * 60   # ueber eine getaktete Verbindung (Handy-Hotspot) seltener
POLL_QUIET = 15 * 60    # in den naechsten BOARD_MIN Minuten faehrt nichts (nachts)
POLL_WINDOW = 60        # solange das Fenster die Abfahrten zeigt
POLL_VAO = 10 * 60      # VOR/OÖVV antworten ungepackt und gross: hoechstens so oft
POLL_MOTIS = 4 * 60     # Transitous laeuft auf Spenden und Freiwilligen: hoechstens so oft
RETRY = 60              # nach einem Fehler; ein Netzwechsel loest ohnehin eine Abfrage aus
TICK = 20               # so oft fallen verpasste Abfahrten aus dem Menue (ohne Abfrage)
LEARN_AGE = 7 * 86400   # so lange gilt, welche Betreiber an einer Haltestelle fahren
BOARD_MIN = 90          # so weit voraus fragt die Abfahrtstafel
BOARD_BEFORE = 3 * 60   # und so weit zurueck - verspaetete Abfahrten fehlten sonst
# Die HAFAS-Abfahrtstafeln bringen die Abfahrten benachbarter Haltestellen mit;
# abschalten laesst sich das nicht. Behalten wird nur, was an der gewaehlten
# Haltestelle abfaehrt; die Tafel ist dafuer so gross, wie es die letzte Antwort
# verlangt hat (gelernt je Haltestelle).
BOARD_START, BOARD_LEAST, BOARD_MOST = 30, 12, 50
BOARD_SPARE = 3
EFA_LIMIT = 20          # Abfahrten je Linz-AG-Abfrage
MOTIS_LIMIT = 24        # Abfahrten je Transitous-Abfrage
# Blendet der Filter Linien aus, muessen die Tafeln weiter reichen, bis genug gezeigte
# dabei sind: die ÖBB-Tafel dann hoechstens so gross (voll ueber 93 Minuten an einem
# Wiener Bahnhof mit U-Bahn, Bim und Bus: rund 100 Abfahrten, 11 statt 7 KB gzip).
# VOR und OÖVV antworten ungepackt - ihre Tafeln bleiben bei BOARD_MOST. Linz AG und
# Transitous lernen ihre Groesse dann wie die HAFAS-Tafeln, ohne Filter bleibt es bei
# EFA_LIMIT bzw. MOTIS_LIMIT.
BOARD_WIDE = 150
EFA_MOST = 60
MOTIS_MOST = 64
# Welche Linien in welche Richtungen an einer Haltestelle fahren (fuer den Filter):
# alle Abfahrten der naechsten SURVEY_MIN Minuten, gemerkt fuer SURVEY_AGE.
SURVEY_MIN = 240
SURVEY_JNY, SURVEY_EFA, SURVEY_MOTIS = 200, 80, 80
SURVEY_AGE = 30 * 60
REACH_SLACK = 30        # s: so knapp darf es fuer "noch erreichbar" sein

# Zuhause und Haltestellen
NEAR_M = 2000           # die naechsten NEAR_MAX Haltestellen in diesem Umkreis stehen zur Wahl
NEAR_MAX = 15
MATCH_M = 300           # so nah muessen gleichnamige Haltestellen zweier Betreiber liegen
MAX_STOPS = 4           # so viele Haltestellen zeigt das Menue hoechstens
DEFAULT_STOPS = 2       # vorgewaehlt: die naechste und eine mit anderen Verkehrsmitteln
DEFAULT_WALK = 8 * 60   # s: weiter weg wird nichts vorgewaehlt
WALK_SPEED = 75         # m je Minute auf Luftlinie * 1,3, wenn kein Router antwortet
MENU_ROWS = 10          # Abfahrtszeilen im Menue insgesamt
SLOTS = 16              # Zeilen ueber dem Trenner (Ueberschriften, Abfahrten, Hinweise)
RECENT_MAX = 6          # zuletzt gesuchte Ziele
SAVED_MAX = 20          # gespeicherte Ziele
LABEL_MAX = 40          # Zeichen fuer den eigenen Namen eines gespeicherten Ziels
TRIPS = 5               # Verbindungen je Suche
ENRICH_LEGS = 3         # so viele Etappen je Suche bekommen Echtzeit vom Betreiber nachgeholt

# Welche Verbindungen sinnvoll sind (Zeiten in Sekunden). Zwei aehnliche Verbindungen
# vergleicht der "Aufwand": Dauer, je Umstieg CHANGE_COST dazu, Fussweg und Rad zu
# EFFORT_FACTOR. Eine andere ersetzt eine Verbindung nur, wenn sie nicht frueher losgeht,
# hoechstens LATER_SLACK spaeter ankommt (LATER_SLACK_WAIT, wenn man dafuer WAIT_GAIN
# spaeter losgeht) und BETTER_BY weniger Aufwand ist.
CHANGE_COST = 5 * 60
EFFORT_FACTOR = 0.5
LATER_SLACK = 3 * 60
LATER_SLACK_WAIT = 5 * 60
WAIT_GAIN = 10 * 60
BETTER_BY = 2 * 60
MORE_ON_FOOT = 2 * 60   # s: so viel mehr Fussweg (und Rad) darf "nicht frueher los, nicht spaeter da" haben
WALK_GAIN = 3 * 60     # Oeffis muessen so viel schneller sein als der ganze Weg zu Fuss ...
WALK_SAVE = 5 * 60      # ... oder so viel Fussweg sparen (bzw. WALK_SAVE_SHARE davon)
WALK_SAVE_SHARE = 0.4
# Rad + Oeffis (Bike & Ride): mit dem Rad zur Haltestelle, hoechstens MIXED_BIKE_MAX und
# mindestens MIXED_BIKE_MIN (kuerzer geht man zu Fuss). Gezeigt nur, wenn es MIXED_GAIN
# (bzw. MIXED_GAIN_SHARE) schneller ist als Oeffis allein und als die ganze Strecke mit
# dem Rad. Naeher als MIXED_NEAR_M faehrt man ganz mit dem Rad - dann keine Abfrage.
MIXED_BIKE_MAX = 20 * 60
MIXED_BIKE_MIN = 3 * 60
MIXED_GAIN = 5 * 60
MIXED_GAIN_SHARE = 0.15
MIXED_NEAR_M = 1500
# Autorouten: die schnellste und Alternativen, die hoechstens ALT_SLOWER (bzw.
# ALT_SLOWER_SHARE) langsamer sind und zu weniger als ALT_SHARED ueber dieselben
# Strassen fuehren wie eine schnellere - zusammen hoechstens ALT_MAX.
ALT_MAX = 3
ALT_SLOWER = 5 * 60
ALT_SLOWER_SHARE = 0.15
ALT_SHARED = 0.7

_CONFIG = os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config")
SETTINGS_FILE = os.path.join(_CONFIG, "transit-tray", "settings.json")
_CACHE = os.path.join(os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache"), "transit-tray")
CACHE_FILE = os.path.join(_CACHE, "departures.json")
TILE_DIR = os.path.join(_CACHE, "tiles")
TILE_MAX_AGE = 30 * 86400
_RUNTIME = os.environ.get("XDG_RUNTIME_DIR")
RUNTIME_DIR = os.path.join(_RUNTIME, "transit-tray") if _RUNTIME else "/tmp/transit-tray-%d" % os.getuid()
ICON_DIR = os.path.join(RUNTIME_DIR, "icons")
LOCK_FILE = os.path.join(RUNTIME_DIR, "lock")            # mit der PID des laufenden Widgets
ACTIVATE_FILE = os.path.join(RUNTIME_DIR, "activate")    # welches Fenster, Aktivierungs-Token
# Logo und Menue-Symbole liegen wie beim Wetter im hicolor-Theme unter
# ~/.local/share/icons - dort findet COSMIC sie auch im Menue.
APP_ICON = "transit-tray"
APP_ICON_DIR = os.path.join(os.environ.get("XDG_DATA_HOME") or os.path.expanduser("~/.local/share"),
                            "icons", "hicolor", "scalable", "apps")

# Platz je Menuezeile wie beim Wetter: libcosmic setzt Statusleisten-Popups auf 360 px,
# jeder Eintrag hat links und rechts 24 px Innenabstand, das Bild davor 14 px plus
# 8 px Abstand, Schrift 14 px. Dazu ein halbes Geviert Reserve - laengere Zeilen
# bricht COSMIC um.
LINE_EM = (360 - 2 * 24 - 14 - 8) / 14.0 - 0.5
MENU_FONT_FILE = os.path.join(_CONFIG, "cosmic", "com.system76.CosmicTk", "v1", "interface_font")
GAP_TIME, GAP_LINE, GAP_EXTRA = 1.1, 0.9, 1.1      # Spaltenabstaende der Abfahrtszeilen in Geviert
REFRESH = "Refresh now"
# Trenner im Menue: drei Leerzeichen je Seite (wie beim Wetter). Die Texte entstehen
# mit " · " (so auch fuer --once), der Tray weitet sie auf.
SEP = "   ·   "
NOTES = {"error": "service error"}
EXIT_CODES = {"ok": 0, "nohome": 2, "offline": 3, "error": 4}

DAYS = ("Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun")
MONTHS = ("Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec")
VIENNA = zoneinfo.ZoneInfo("Europe/Vienna")

# Fehlercodes von HAFAS, die "nichts gefunden" heissen, mit einem Satz fuers Fenster.
HAFAS_NO_RESULT = {
    "H890": "No connections found.", "H891": "No connections found.", "H899": "No connections found.",
    "H9240": "No connections found.", "SQ005": "No connections found.", "TI001": "No connections found.",
    "H892": "The search was too complex. Try another time.",
    "H895": "Start and destination are too close to each other.",
    "H9380": "Start and destination are too close to each other.",
    "H9220": "No stops near the start or the destination.",
    "H9260": "The start is not known to the timetable.", "H9300": "The destination is not known to the timetable.",
    "H9360": "This date is outside the timetable.", "SQ001": "No departures known.",
    "LOCATION": "A place was not found.",
}

# Erst im Tray-Modus geladen (load_gtk), damit --once auch ohne Anzeige laeuft.
AppIndicator = Gdk = GdkPixbuf = Gio = GLib = Gtk = Pango = PangoCairo = None


def log(msg):
    print("transit-tray: %s" % msg, file=sys.stderr, flush=True)


_ZONES = {}


def zone(name):
    """Zeitzone nach Name ('Europe/Lisbon'); ohne Namen Wien - die Auskuenfte in
    Oesterreich rechnen in Wiener Zeit."""
    if not name:
        return VIENNA
    if name not in _ZONES:
        try:
            _ZONES[name] = zoneinfo.ZoneInfo(name)
        except (zoneinfo.ZoneInfoNotFoundError, ValueError):
            _ZONES[name] = VIENNA
    return _ZONES[name]


# ------------------------------------------------------------------ Abruf

class Offline(Exception):
    """Dienst nicht erreichbar (kein Netz, DNS, Timeout)."""


class ServiceError(Exception):
    """Unerwartete Antwort eines Diensts."""


class NoResult(Exception):
    """Die Auskunft hat nichts gefunden - der Text sagt es dem Benutzer."""


class KeyRejected(ServiceError):
    """TomTom lehnt den Schluessel ab."""


def _read(resp):
    raw = resp.read()
    if (resp.headers.get("Content-Encoding") or "").lower() == "gzip":
        raw = gzip.decompress(raw)
    return raw


def request_raw(url, body=None, params=None, headers=None):
    """GET (ohne body) oder POST mit JSON -> Bytes. gzip spart am Hotspot rund vier
    Fuenftel (wo der Dienst es kann)."""
    if params:
        url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    head = dict(HEADERS, **(headers or {}))
    data = None
    if body is not None:
        data = json.dumps(body, separators=(",", ":")).encode("utf-8")
        head["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=head)
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
            return _read(resp)
    except urllib.error.HTTPError as exc:
        try:
            detail = json.loads(_read(exc) or b"{}")
        except (OSError, ValueError, EOFError):
            detail = {}
        exc.close()
        if not isinstance(detail, dict):
            detail = {}
        if detail.get("code") in ("NoRoute", "NoSegment"):
            raise NoResult("No route found.") from exc     # OSRM: Ziel nicht erreichbar
        if exc.code in (401, 403) and "tomtom" in url:
            raise KeyRejected("TomTom rejected the key (HTTP %d)." % exc.code) from exc
        text = ((detail.get("error") or {}).get("description") if isinstance(detail.get("error"), dict) else None) \
            or ((detail.get("detailedError") or {}).get("message") if isinstance(detail.get("detailedError"), dict)
                else None) or detail.get("message") or ""
        raise ServiceError("HTTP %s %s" % (exc.code, text)) from exc
    except (urllib.error.URLError, http.client.HTTPException, OSError, EOFError) as exc:
        raise Offline(str(getattr(exc, "reason", None) or exc)) from exc


def request_json(url, body=None, params=None, headers=None):
    raw = request_raw(url, body, params, headers)
    try:
        return json.loads(raw)
    except ValueError as exc:
        raise ServiceError("no JSON in the answer") from exc


def run_parallel(jobs, workers=4):
    """{name: Funktion} gleichzeitig ausfuehren -> {name: Ergebnis oder Ausnahme}."""
    out = {}
    if not jobs:
        return out
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(workers, len(jobs))) as pool:
        futures = {pool.submit(fn): name for name, fn in jobs.items()}
        for future in concurrent.futures.as_completed(futures):
            try:
                out[futures[future]] = future.result()
            except Exception as exc:  # noqa: BLE001 - jede Quelle fuer sich
                out[futures[future]] = exc
    return out


# ------------------------------------------------------------------ HAFAS (ÖBB, VOR, OÖVV)

def hafas(source, *calls):
    """Anfragen an eine HAFAS-Auskunft, mehrere in einem Aufruf: hafas("oebb",
    ("StationBoard", {...}), ...) -> [Antwort je Anfrage]. Scheitert nur eine Anfrage,
    steht an ihrer Stelle die Ausnahme (NoResult oder ServiceError)."""
    cfg = HAFAS_SOURCES[source]
    data = request_json(cfg["url"], dict(cfg["base"], svcReqL=[{"meth": m, "req": r} for m, r in calls]))
    if not isinstance(data, dict):
        raise ServiceError("%s: no object in the answer" % SOURCE_NAMES[source])
    if data.get("err") not in (None, "OK"):
        raise ServiceError("%s: %s %s" % (SOURCE_NAMES[source], data.get("err"),
                                         data.get("errTxt") or data.get("hammError") or ""))
    results = data.get("svcResL")
    if not isinstance(results, list) or len(results) != len(calls):
        raise ServiceError("%s: %d answers for %d requests" % (SOURCE_NAMES[source], len(results or []), len(calls)))
    out = []
    for res in results:
        err = res.get("err") if isinstance(res, dict) else "?"
        if err in (None, "OK"):
            out.append(res.get("res") or {})
        elif err in HAFAS_NO_RESULT:
            out.append(NoResult(HAFAS_NO_RESULT[err]))
        else:
            out.append(ServiceError("%s %s: %s" % (SOURCE_NAMES[source], err, res.get("errTxt") or "")))
    return out


def hafas_one(source, meth, req):
    res = hafas(source, (meth, req))[0]
    if isinstance(res, Exception):
        raise res
    return res


def pick(items, index):
    """items[index] fuer Verweise in HAFAS-Antworten (locX, prodX) - {} wenn es ihn nicht gibt."""
    if isinstance(index, int) and isinstance(items, list) and 0 <= index < len(items) \
            and isinstance(items[index], dict):
        return items[index]
    return {}


def hafas_time(date, text, offset=None):
    """'20261002' + '174000' -> Unix-Zeit. Vor der Uhrzeit koennen Tage stehen
    ('01003000' = 00:30 am Folgetag). offset: Zeitzone der Haltestelle in Minuten."""
    if not date or not text:
        return None
    text = str(text)
    try:
        days = int(text[:-6] or 0)
        hour, minute, second = int(text[-6:-4]), int(text[-4:-2]), int(text[-2:])
        day = dt.date(int(date[:4]), int(date[4:6]), int(date[6:8])) + dt.timedelta(days=days)
        tz = dt.timezone(dt.timedelta(minutes=offset)) if isinstance(offset, int) else VIENNA
        return dt.datetime(day.year, day.month, day.day, hour, minute, second, tzinfo=tz).timestamp()
    except (ValueError, TypeError, IndexError):
        return None


def hafas_seconds(text):
    """Dauer '000400' (oder mit Tagen davor) -> Sekunden."""
    if not text:
        return None
    text = str(text)
    try:
        return int(text[:-6] or 0) * 86400 + int(text[-6:-4]) * 3600 + int(text[-4:-2]) * 60 + int(text[-2:])
    except (ValueError, IndexError):
        return None


def hafas_coord(loc):
    crd = (loc or {}).get("crd") or {}
    if isinstance(crd.get("x"), int) and isinstance(crd.get("y"), int):
        return (crd["x"] / 1e6, crd["y"] / 1e6)
    return None


def decode_polyline(text, precision=5):
    """Google-Polyline (Breite, Laenge) -> [(lon, lat)]."""
    points, index, lat, lon = [], 0, 0, 0
    factor = 10.0 ** precision
    try:
        while index < len(text):
            for which in (0, 1):
                shift = result = 0
                while True:
                    byte = ord(text[index]) - 63
                    index += 1
                    result |= (byte & 0x1f) << shift
                    shift += 5
                    if byte < 0x20:
                        break
                delta = ~(result >> 1) if result & 1 else result >> 1
                if which == 0:
                    lat += delta
                else:
                    lon += delta
            points.append((lon / factor, lat / factor))
    except IndexError:
        pass
    return points


def hafas_path(common, ref):
    """Streckenverlauf einer Etappe aus polyG -> [(lon, lat)]."""
    polys = common.get("polyL") or []
    path = []
    for index in ((ref or {}).get("polyG") or {}).get("polyXL") or []:
        poly = pick(polys, index)
        if poly.get("crdEncYX"):
            path.extend(decode_polyline(poly["crdEncYX"]))
    return path


def kind_of(cls):
    """Verkehrsmittel nach der Produktklasse der ÖBB-Auskunft (Bitmaske): Strassenbahn
    512, U-Bahn 256, Bus 64, Rufbus 1024, Schiff 128 - alles andere (Fernzug, REX, R,
    S-Bahn, Westbahn ...) ist ein Zug."""
    cls = cls if isinstance(cls, int) else 0
    if cls & 512:
        return "tram"
    if cls & 256:
        return "subway"
    if cls & (64 | 1024):
        return "bus"
    if cls & 128:
        return "ferry"
    return "train"


def kinds_of(pcls):
    """Alle Verkehrsmittel einer Haltestelle (pCls), Zug zuerst, Bus zuletzt."""
    found = []
    pcls = pcls if isinstance(pcls, int) else 0
    for bit in (1, 2, 4, 8, 16, 32, 2048, 4096, 256, 512, 64, 1024, 128):
        if pcls & bit and kind_of(bit) not in found:
            found.append(kind_of(bit))
    return found


def product_kind(prod, common):
    """Verkehrsmittel einer Linie: nach dem Symbol der Auskunft (VAO zaehlt die Klassen
    anders als die ÖBB), sonst nach der Klasse."""
    res = str(pick(common.get("icoL") or [], prod.get("icoX")).get("res") or "")
    for word, kind in (("tram", "tram"), ("prod_sub", "subway"), ("ubahn", "subway"), ("bus", "bus"),
                       ("ship", "ferry"), ("boat", "ferry"), ("comm", "train"), ("ice", "train"),
                       ("reg", "train"), ("ic", "train"), ("rail", "train"), ("train", "train")):
        if word in res:
            return kind
    return kind_of(prod.get("cls"))


def line_label(prod, kind):
    """Kurzname der Linie: '1', '27', 'U1', 'S2', 'REX 4', 'WB 922'."""
    ctx = prod.get("prodCtx") or {}
    line = str(ctx.get("line") or prod.get("number") or "").strip()
    name = re.sub(r"\s*\(Zug-Nr\.[^)]*\)", "", str(prod.get("name") or "")).strip()
    cat = str(ctx.get("catOut") or "").strip()
    if kind != "train" and line:
        return line
    if cat == "S" and line:
        return "S" + line
    if kind != "train" and name:
        return re.sub(r"^(Tram|Straßenbahn|Stadtbus|Regionalbus|Bus|O-Bus|Autobus|Nachtbus)\s+", "", name)
    return name or line or cat or "?"


def operator_of(prod, common):
    return pick(common.get("opL") or [], prod.get("oprX")).get("name") or ""


def platform(stop, prefix):
    """Gleis bzw. Steig: (planmaessig, tatsaechlich - nur wenn anders)."""
    planned = (stop.get(prefix + "PltfS") or {}).get("txt") or stop.get(prefix + "PlatfS")
    real = (stop.get(prefix + "PltfR") or {}).get("txt") or stop.get(prefix + "PlatfR")
    return planned, (real if real and real != planned else None)


def direction_flag(flag, valid=("H", "R")):
    """Richtung einer Linie, wie sie der Betreiber kennzeichnet: H/R (Hin- und
    Rueckrichtung) bei Wiener Linien, Linz AG und den Stadtlinien der ÖBB-Tafel, 0/1 bei
    Transitous (GTFS). Fernzuege tragen bei der ÖBB "x", manche Busse 0 oder 2 ohne
    feste Bedeutung - dann None, und es zaehlt das Ziel."""
    flag = str(flag if flag is not None else "").strip()
    return flag if flag in valid else None


def parse_board(res, source):
    """Abfahrten aus StationBoard, nach tatsaechlicher Zeit sortiert."""
    common = res.get("common") or {}
    prods, locs = common.get("prodL") or [], common.get("locL") or []
    out = []
    for j in res.get("jnyL") or []:
        stop = j.get("stbStop") or {}
        date = j.get("date")
        planned = hafas_time(date, stop.get("dTimeS"), stop.get("dTZOffset"))
        if planned is None:
            continue
        prod = pick(prods, j.get("prodX"))
        kind = product_kind(prod, common)
        plat, plat_new = platform(stop, "d")
        out.append({"line": line_label(prod, kind), "kind": kind,
                    "direction": str(j.get("dirTxt") or "").strip(), "dir": direction_flag(j.get("dirFlg")),
                    "planned": planned,
                    "real": hafas_time(date, stop.get("dTimeR"), stop.get("dTZOffset")),
                    "cancelled": bool(stop.get("dCncl") or j.get("isCncl")),
                    "platform": plat_new or plat, "platform_changed": bool(plat_new),
                    "jid": j.get("jid"), "at": pick(locs, stop.get("locX")).get("name") or "",
                    "source": source, "operator": operator_of(prod, common)})
    out.sort(key=lambda d: (eff_time(d), d["line"]))
    return out


def hafas_board(source, lid, now, size, extra=None):
    start = dt.datetime.fromtimestamp(now - BOARD_BEFORE, VIENNA)
    req = {"type": "DEP", "date": start.strftime("%Y%m%d"), "time": start.strftime("%H%M%S"),
           "stbLoc": {"lid": lid, "type": "S"}, "maxJny": size, "dur": BOARD_MIN + BOARD_BEFORE // 60}
    if source != "oebb":
        req["pslMode"] = "OFF"          # VAO braechte sonst jeden Halt jeder Fahrt mit (267 KB)
    req.update(extra or {})
    return ("StationBoard", req)


# ------------------------------------------------------------------ EFA (Wiener Linien, Linz AG)

EFA_COORD = "%.6f:%.6f:WGS84[DD.ddddd]"
# EFA-Verkehrsmittel (motType): 0 Zug, 1 S-Bahn, 2 U-Bahn, 3 Stadtbahn, 4 Strassenbahn,
# 5 Stadtbus, 6 Regionalbus, 7 Schnellbus, 8 Seil-/Zahnradbahn, 9 Schiff, 10 Rufbus,
# 11 sonstige; ab 97 Fusswege und Umstiege.
EFA_KINDS = {"0": "train", "1": "train", "2": "subway", "3": "tram", "4": "tram", "5": "bus", "6": "bus",
             "7": "bus", "8": "tram", "9": "ferry", "10": "bus", "11": "bus", "13": "train", "14": "train",
             "15": "train", "16": "train", "17": "bus", "18": "train", "19": "bus"}
# Verkehrsmittel einer Haltestelle in der Umkreissuche (STOP_MEANS_LIST)
EFA_MEANS = {"0": "train", "1": "train", "2": "subway", "3": "bus", "4": "tram", "5": "bus", "6": "bus",
             "7": "bus", "8": "tram", "9": "ferry", "16": "bus"}


def efa_kind(item):
    """Verkehrsmittel einer EFA-Linie nach ihrem Produktnamen ("U-Bahn", "Straßenbahn",
    "Stadtbus" ...). Die Nummern dazu (type, motType) zaehlen je Betreiber anders: bei den
    Wiener Linien ist 1 die U-Bahn und 2 die S-Bahn, bei der Linz AG 11 die Bergbahn."""
    words = " ".join(str(item.get(k) or "") for k in ("product", "name")).lower()
    if "u-bahn" in words:
        return "subway"
    if any(w in words for w in ("straßenbahn", "strassenbahn", "tram", "bergbahn", "seilbahn", "zahnradbahn")):
        return "tram"
    if any(w in words for w in ("s-bahn", "zug", "railjet", "regionalexpress", "bahn")):
        return "train"
    if any(w in words for w in ("bus", "taxi")):
        return "bus"
    if any(w in words for w in ("schiff", "fähre", "faehre")):
        return "ferry"
    return EFA_KINDS.get(str(item.get("motType") or item.get("type") or ""), "bus")


def efa(source, endpoint, params):
    params = [("outputFormat", "JSON"), ("coordOutputFormat", "WGS84[DD.ddddd]"),
              ("locationServerActive", "1")] + list(params)
    data = request_json("%s/%s" % (EFA_SOURCES[source], endpoint), params=params)
    if not isinstance(data, dict):
        raise ServiceError("%s: no object in the answer" % SOURCE_NAMES[source])
    return data


def efa_stamp(stamp, real=False):
    """EFA 'stamp' {'date': '20261002', 'timeSec': '191300', 'rtDate', 'rtTimeSec'} -> Unix-Zeit."""
    if not isinstance(stamp, dict):
        return None
    if real:
        return hafas_time(stamp.get("rtDate"), stamp.get("rtTimeSec") or ((stamp.get("rtTime") or "") + "00"))
    return hafas_time(stamp.get("date"), stamp.get("timeSec") or ((stamp.get("time") or "") + "00"))


def efa_datetime(d):
    """EFA {'year', 'month', 'day', 'hour', 'minute'} -> Unix-Zeit."""
    try:
        return dt.datetime(int(d["year"]), int(d["month"]), int(d["day"]), int(d["hour"]), int(d["minute"]),
                           tzinfo=VIENNA).timestamp()
    except (KeyError, TypeError, ValueError):
        return None


def efa_coord(text):
    try:
        lon, lat = (float(v) for v in str(text).split(",")[:2])
        return (lon, lat)
    except (ValueError, TypeError):
        return None


def efa_path(text):
    return [c for c in (efa_coord(p) for p in str(text or "").split()) if c]


def efa_nearby(source, lat, lon, radius=NEAR_M, limit=30):
    """Haltestellen im Umkreis (XML_COORD_REQUEST): [{"id", "name", "gid", "coord", "distance", "kinds"}]."""
    data = efa(source, "XML_COORD_REQUEST", [("coord", EFA_COORD % (lon, lat)), ("inclFilter", "1"),
                                             ("type_1", "STOP"), ("radius_1", str(int(radius))),
                                             ("max", str(limit))])
    out = []
    for pin in data.get("pins") or []:
        attrs = {a.get("name"): a.get("value") for a in pin.get("attrs") or [] if isinstance(a, dict)}
        coord = efa_coord(pin.get("coords"))
        if not pin.get("id") or not coord:
            continue
        kinds = []
        for mean in str(attrs.get("STOP_MEANS_LIST") or "").split(","):
            kind = EFA_MEANS.get(mean.strip())
            if kind and kind not in kinds:
                kinds.append(kind)
        out.append({"id": str(pin["id"]), "name": str(pin.get("desc") or ""), "gid": attrs.get("STOP_GLOBAL_ID"),
                    "coord": coord, "distance": float(pin.get("distance") or 0), "kinds": kinds,
                    "locality": str(pin.get("locality") or "")})
    return out


def efa_departures(source, stop_id, now, limit=EFA_LIMIT):
    """Abfahrten einer Haltestelle mit Echtzeit (XML_DM_REQUEST), ab kurz vor jetzt."""
    start = dt.datetime.fromtimestamp(now - BOARD_BEFORE, VIENNA)
    data = efa(source, "XML_DM_REQUEST", [("type_dm", "stop"), ("name_dm", stop_id), ("mode", "direct"),
                                          ("useRealtime", "1"), ("limit", str(limit)),
                                          ("itdDate", start.strftime("%Y%m%d")), ("itdTime", start.strftime("%H%M"))])
    out = []
    for dep in data.get("departureList") or []:
        line = dep.get("servingLine") or {}
        planned = efa_datetime(dep.get("dateTime"))
        if planned is None:
            continue
        real = efa_datetime(dep.get("realDateTime")) if dep.get("realDateTime") else None
        status = str(dep.get("realtimeTripStatus") or "").upper()
        out.append({"line": str(line.get("number") or line.get("symbol") or "?"),
                    "kind": efa_kind(line),
                    "direction": str(line.get("direction") or "").strip(),
                    "dir": direction_flag((line.get("liErgRiProj") or {}).get("direction")), "planned": planned,
                    "real": real if line.get("realtime") == "1" or real else None,
                    "cancelled": "CANCEL" in status, "platform": None, "platform_changed": False, "jid": None,
                    "at": str(dep.get("stopName") or ""), "source": source,
                    "operator": str((dep.get("operator") or {}).get("name") or SOURCE_NAMES[source])})
    out = [d for d in out if d["planned"] <= now + 4 * 3600]     # nicht bis zum naechsten Morgen
    out.sort(key=lambda d: (eff_time(d), d["line"]))
    return out


EFA_WALK = ("97", "98", "99", "100", "101", "102", "103", "104", "105", "106", "107")


def efa_trips(source, origin, destination, moment, arrive):
    """Verbindungen aus dem Routenplaner (XML_TRIP_REQUEST2) mit Echtzeit und Strecke."""
    local = dt.datetime.fromtimestamp(moment, VIENNA)
    data = efa(source, "XML_TRIP_REQUEST2", [
        ("type_origin", "coord"), ("name_origin", EFA_COORD % (origin["longitude"], origin["latitude"])),
        ("type_destination", "coord"), ("name_destination", EFA_COORD % (destination["longitude"], destination["latitude"])),
        ("itdDate", local.strftime("%Y%m%d")), ("itdTime", local.strftime("%H%M")),
        ("itdTripDateTimeDepArr", "arr" if arrive else "dep"), ("useRealtime", "1"),
        ("calcNumberOfTrips", str(TRIPS)), ("routeType", "LEASTTIME"), ("changeSpeed", "normal")])
    trips = data.get("trips")
    if isinstance(trips, dict):                 # EFA liefert einen einzelnen Treffer manchmal ohne Liste
        trips = trips.get("trip")
        trips = trips if isinstance(trips, list) else [trips] if trips else []
    cons = [c for c in (parse_efa_trip(t, source) for t in trips or [] if isinstance(t, dict)) if c]
    # Die EFA bringt auch Fahrten von kurz vor der Zeit mit (bei "jetzt" schon weg) - nur
    # was ab der Zeit losgeht bzw. bis zu ihr ankommt (eine Minute Spiel: sie rechnet in Minuten)
    if arrive:
        cons = [c for c in cons if eff_time(c, "arr") <= moment + 60]
    else:
        cons = [c for c in cons if eff_time(c, "dep") >= moment - 60]
    if not cons:
        raise NoResult("No connections found.")
    return cons


EFA_LEVELS = {"STAIRS": "stairs", "ESCALATOR": "escalator", "ELEVATOR": "lift", "LIFT": "lift", "RAMP": "ramp"}


def efa_transfer(leg):
    """Der Umstiegsweg nach einer Fahrt, wie ihn die EFA an die Fahrt haengt: Minuten
    ("footpath" mit Position AFTER), Strecke ("interchange") und das erste Hinauf oder
    Hinunter ("stairs up"). -> (Sekunden, Strecke, Hinweis) oder None"""
    feet = leg.get("footpath") or []
    feet = [feet] if isinstance(feet, dict) else feet
    foot = next((f for f in feet if isinstance(f, dict) and f.get("position") == "AFTER"), None)
    if foot is None:
        return None
    try:
        seconds = int(round(float(foot.get("duration") or 0) * 60))
    except (TypeError, ValueError):
        return None
    if seconds <= 0:
        return None
    hint = None
    elems = foot.get("footpathElem") or []
    for elem in [elems] if isinstance(elems, dict) else elems:
        word = EFA_LEVELS.get(str(elem.get("type") or "").upper()) if isinstance(elem, dict) else None
        way = {"UP": "up", "DOWN": "down"}.get(str(elem.get("level") or "").upper()) if word else None
        if way:
            hint = "%s %s" % (word, way)
            break
    return seconds, efa_path((leg.get("interchange") or {}).get("path")), hint


def transfer_leg(came, going, seconds, path, hint):
    """Fussweg zwischen zwei Fahrten: vom Ausstieg (Steig) zum Einstieg, so lange wie
    der Planer rechnet."""
    start, end = came.get("to_coord"), going.get("from_coord")
    path = list(path)
    if start and (not path or distance_m(start[1], start[0], path[0][1], path[0][0]) > 5):
        path.insert(0, start)
    if end and (not path or distance_m(end[1], end[0], path[-1][1], path[-1][0]) > 5):
        path.append(end)
    meters = sum(distance_m(a[1], a[0], b[1], b[0]) for a, b in zip(path, path[1:]))
    return {"type": "walk", "transfer": True, "from": came["to"], "to": going["from"],
            "dep": came["arr"], "dep_real": came.get("arr_real"), "arr": came["arr"] + seconds,
            "arr_real": came["arr_real"] + seconds if came.get("arr_real") is not None else None,
            "from_coord": start, "to_coord": end, "path": path, "duration": seconds,
            "distance": round(meters) if meters >= 1 else None, "levels": hint}


def parse_efa_trip(trip, source):
    legs = []
    for leg in trip.get("legs") or []:
        mode = leg.get("mode") or {}
        points = leg.get("points") or []
        if isinstance(points, dict):
            points = points.get("point") or []
        if len(points) < 2:
            continue
        first, last = points[0], points[-1]
        dep, arr = efa_stamp(first.get("stamp")), efa_stamp(last.get("stamp"))
        if dep is None or arr is None:
            continue
        dep_rt, arr_rt = efa_stamp(first.get("stamp"), True), efa_stamp(last.get("stamp"), True)
        path = efa_path(leg.get("path"))
        item = {"from": str(first.get("name") or ""), "to": str(last.get("name") or ""),
                "dep": dep, "dep_real": dep_rt if dep_rt not in (None, dep) else None,
                "arr": arr, "arr_real": arr_rt if arr_rt not in (None, arr) else None,
                "from_coord": efa_coord((first.get("ref") or {}).get("coords")) or (path[0] if path else None),
                "to_coord": efa_coord((last.get("ref") or {}).get("coords")) or (path[-1] if path else None),
                "path": path}
        typ = str(mode.get("type") or "")
        if typ in EFA_WALK or str(mode.get("code")) == "-1":
            meters = sum(distance_m(a[1], a[0], b[1], b[0]) for a, b in zip(path, path[1:]))
            item.update(type="walk", duration=(eff_time(item, "arr") - eff_time(item, "dep")),
                        distance=round(meters) if meters else None)
        else:
            stops = []
            for st in (leg.get("stopSeq") or [])[1:-1]:
                ref = st.get("ref") or {}
                when = ref.get("depDateTimeSec") or ref.get("arrDateTimeSec") or ""
                parts = when.replace(":", "").split()
                planned = hafas_time(parts[0], parts[1]) if len(parts) == 2 else None
                delay = ref.get("depDelay") or ref.get("arrDelay")
                try:
                    real = planned + int(delay) * 60 if planned is not None and delay not in (None, "", "-9999") else None
                except ValueError:
                    real = None
                stops.append({"name": str(st.get("name") or ""), "time": planned, "real": real,
                              "coord": efa_coord(ref.get("coords")), "cancelled": False})
            diva = mode.get("diva") or {}
            item.update(type="ride", line=str(mode.get("number") or mode.get("symbol") or "?"),
                        kind=efa_kind(mode), direction=str(mode.get("destination") or "").strip(),
                        stops=stops, cancelled=str(leg.get("realtimeStatus") or "").upper().find("CANCEL") >= 0,
                        operator=str(diva.get("operator") or SOURCE_NAMES[source]),
                        dep_platform=None, arr_platform=None, dep_platform_changed=False,
                        arr_platform_changed=False, reachable=True,
                        rt_source=SOURCE_NAMES[source] if mode.get("realtime") == "1" else None)
            item["transfer"] = efa_transfer(leg)
        legs.append(item)
    if not legs or not any(l["type"] == "ride" for l in legs):
        return None
    # Umstieg an derselben Haltestelle, aber an anderer Stelle (U-Bahn-Steig unten, Bim
    # oben): die EFA haengt den Weg nur an die Fahrt davor - hier wird er ein Fussweg
    joined = []
    for i, item in enumerate(legs):
        joined.append(item)
        walk = item.pop("transfer", None)
        going = legs[i + 1] if i + 1 < len(legs) else None
        if walk and going is not None and going["type"] == "ride":
            joined.append(transfer_leg(item, going, *walk))
    legs = joined
    return {"dep": legs[0]["dep"], "dep_real": legs[0].get("dep_real"), "arr": legs[-1]["arr"],
            "arr_real": legs[-1].get("arr_real"), "changes": max(0, sum(1 for l in legs if l["type"] == "ride") - 1),
            "legs": legs, "cancelled": any(l.get("cancelled") for l in legs), "reachable": True, "planner": source}


# ------------------------------------------------------------------ Wiener Linien (Open Data)

WL_KINDS = {"ptMetro": "subway", "ptTram": "tram", "ptTramWLB": "tram", "ptBusCity": "bus",
            "ptBusNight": "bus", "ptBusRegion": "bus", "ptTrainS": "train", "ptTrain": "train"}


def iso_time(text):
    """'2026-10-02T19:05:00.000+0200' -> Unix-Zeit."""
    if not text:
        return None
    text = re.sub(r"([+-]\d{2})(\d{2})$", r"\1:\2", str(text))
    try:
        return dt.datetime.fromisoformat(text.replace("Z", "+00:00")).timestamp()
    except ValueError:
        return None


def wl_departures(divas, now):
    """Echtzeit-Abfahrten der Wiener Linien je Haltestelle (DIVA), alle Steige auf einmal.
    -> {diva: [Abfahrten]}"""
    data = request_json(WL_MONITOR, params=[("diva", d) for d in divas])
    monitors = ((data.get("data") or {}).get("monitors")) if isinstance(data, dict) else None
    if monitors is None:
        raise ServiceError("Wiener Linien: %s" % ((data.get("message") or {}).get("value") if isinstance(data, dict)
                                                  else "no data"))
    out = {str(d): [] for d in divas}
    for mon in monitors:
        stop = mon.get("locationStop") or {}
        props = stop.get("properties") or {}
        diva = str(props.get("name") or "")
        title = str(props.get("title") or "")
        for line in mon.get("lines") or []:
            realtime = line.get("realtimeSupported", True)
            for dep in ((line.get("departures") or {}).get("departure")) or []:
                when = dep.get("departureTime") or {}
                vehicle = dep.get("vehicle") or {}
                planned, real = iso_time(when.get("timePlanned")), iso_time(when.get("timeReal"))
                if planned is None and real is None:
                    if when.get("countdown") is None:
                        continue
                    planned = now + int(when["countdown"]) * 60
                direction = re.sub(r"\s+", " ", str(vehicle.get("towards") or line.get("towards") or "")).strip()
                direction = re.sub(r"(\s+[SU])+$", "", direction)        # "Westbahnhof S U": Umsteigen zu S und U
                out.setdefault(diva, []).append({
                    "line": str(vehicle.get("name") or line.get("name") or "?"),
                    "kind": WL_KINDS.get(vehicle.get("type") or line.get("type"), "bus"),
                    "direction": direction.title() if direction.isupper() else direction,
                    "dir": direction_flag(line.get("direction")),
                    "planned": planned if planned is not None else real,
                    "real": real if realtime and real is not None else None, "cancelled": False,
                    "platform": None, "platform_changed": False, "jid": None, "at": title, "source": "wl",
                    "operator": "Wiener Linien",
                    "barrier_free": bool(vehicle.get("barrierFree", line.get("barrierFree")))})
    for deps in out.values():
        deps.sort(key=lambda d: (eff_time(d), d["line"]))
    return out


# ------------------------------------------------------------------ Transitous (ganz Europa)

# Verkehrsmittel bei MOTIS -> unsere; Mitfahrboersen, Leihraeder und Fluege fallen weg
MOTIS_KINDS = {"SUBWAY": "subway", "METRO": "subway", "TRAM": "tram", "CABLE_CAR": "tram", "FUNICULAR": "tram",
               "AERIAL_LIFT": "tram", "BUS": "bus", "COACH": "bus", "ODM": "bus", "FERRY": "ferry",
               "RAIL": "train", "HIGHSPEED_RAIL": "train", "LONG_DISTANCE": "train", "NIGHT_RAIL": "train",
               "REGIONAL_FAST_RAIL": "train", "REGIONAL_RAIL": "train", "SUBURBAN": "train"}
KIND_ORDER = ("train", "subway", "tram", "bus", "ferry")
MOTIS_PLACE_TYPES = {"STOP": "S", "ADDRESS": "A", "PLACE": "P"}


def motis(path, params):
    """Eine Anfrage an Transitous (MOTIS 2) -> JSON."""
    data = request_json(MOTIS_URL + path, params=params)
    if not isinstance(data, (dict, list)):
        raise ServiceError("Transitous: unexpected answer")
    return data


def motis_utc(ts):
    return dt.datetime.fromtimestamp(ts, dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def motis_coord(place):
    try:
        return (float(place["lon"]), float(place["lat"]))
    except (KeyError, TypeError, ValueError):
        return None


def motis_kinds(modes):
    """Verkehrsmittel einer Haltestelle aus ihren MOTIS-Modi, Zug zuerst, Bus zuletzt."""
    found = {MOTIS_KINDS[m] for m in modes or [] if m in MOTIS_KINDS}
    return [k for k in KIND_ORDER if k in found]


def motis_line(item):
    """Die Linie, wie sie am Fahrzeug steht: 'U6', 'S1', 'ICE 597', '144'."""
    return str(item.get("displayName") or item.get("routeShortName") or item.get("tripShortName") or "?").strip()


def motis_track(place):
    """(Gleis bzw. Steig, geaendert?)"""
    track, planned = place.get("track"), place.get("scheduledTrack")
    return (track or planned or None), bool(track and planned and track != planned)


def motis_point(place):
    """Start oder Ziel: die Haltestelle, wenn Transitous sie kennt, sonst Koordinaten."""
    return place.get("motis") or "%.6f,%.6f" % (place["latitude"], place["longitude"])


def motis_departures(stop_id, now, limit=MOTIS_LIMIT):
    """Abfahrten an einer Haltestelle - mit allen gleichnamigen Steigen."""
    data = motis("/v6/stoptimes", [("stopId", stop_id), ("time", motis_utc(now - BOARD_BEFORE)),
                                   ("n", str(limit)), ("withAlerts", "false"), ("language", "de")])
    out = []
    for st in (data.get("stopTimes") or []) if isinstance(data, dict) else []:
        place = st.get("place") or {}
        planned = iso_time(place.get("scheduledDeparture"))
        if planned is None or st.get("mode") not in MOTIS_KINDS or place.get("pickupType") == "NOT_ALLOWED":
            continue                            # endet hier, oder eine Mitfahrboerse
        track, changed = motis_track(place)
        out.append({"line": motis_line(st), "kind": MOTIS_KINDS[st["mode"]],
                    "direction": str(st.get("headsign") or (st.get("tripTo") or {}).get("name") or "").strip(),
                    "dir": direction_flag(st.get("directionId"), ("0", "1")), "planned": planned,
                    "real": iso_time(place.get("departure")) if st.get("realTime") else None,
                    "cancelled": bool(st.get("cancelled") or st.get("tripCancelled") or place.get("cancelled")),
                    "platform": track, "platform_changed": changed, "jid": st.get("tripId"),
                    "at": str(place.get("name") or ""), "source": "motis",
                    "operator": str(st.get("agencyName") or ""), "tz": place.get("tz")})
    out.sort(key=lambda d: (eff_time(d), d["line"]))
    return out


def motis_trip(trip_id):
    """Alle Halte einer Fahrt mit Zeiten und Strecke (wie journey_details)."""
    data = motis("/v6/trip", [("tripId", trip_id), ("language", "de")])
    legs = [l for l in (data.get("legs") or []) if l.get("mode") in MOTIS_KINDS] if isinstance(data, dict) else []
    stops, path = [], []
    for leg in legs:
        live = bool(leg.get("realTime"))
        places = [leg.get("from") or {}] + list(leg.get("intermediateStops") or []) + [leg.get("to") or {}]
        for n, place in enumerate(places):
            track, _new = motis_track(place)
            stop = {"name": str(place.get("name") or ""), "coord": motis_coord(place),
                    "arr": iso_time(place.get("scheduledArrival")),
                    "arr_real": iso_time(place.get("arrival")) if live else None,
                    "dep": iso_time(place.get("scheduledDeparture")),
                    "dep_real": iso_time(place.get("departure")) if live else None,
                    "cancelled": bool(place.get("cancelled")), "platform": track, "tz": place.get("tz")}
            if n == 0 and stops and stops[-1]["name"] == stop["name"]:     # Fahrt geht unter neuer Nummer weiter
                stops[-1].update(dep=stop["dep"], dep_real=stop["dep_real"])
                continue
            stops.append(stop)
        geometry = leg.get("legGeometry") or {}
        path += decode_polyline(geometry.get("points") or "", int(geometry.get("precision") or 6))
    if not stops:
        raise NoResult("No stops known for this trip.")
    return {"direction": str(legs[-1].get("headsign") or stops[-1]["name"]), "stops": stops,
            "path": path if len(path) >= 2 else [s["coord"] for s in stops if s["coord"]]}


def motis_trips(origin, destination, moment, arrive):
    """Verbindungen von Transitous (hoechstens ein paar mehr als TRIPS - ihre Seiten zum
    Blaettern bringen sonst Dutzende auf einmal)."""
    data = motis("/v6/plan", [("fromPlace", motis_point(origin)), ("toPlace", motis_point(destination)),
                              ("time", motis_utc(moment)), ("arriveBy", "true" if arrive else "false"),
                              ("numItineraries", str(TRIPS)), ("maxItineraries", str(TRIPS + 3)),
                              ("language", "de")])
    found = (data.get("itineraries") or []) if isinstance(data, dict) else []
    cons = [c for c in (parse_motis_itinerary(it) for it in found) if c]
    if not cons:
        raise NoResult("No connections found.")
    return cons


def parse_motis_itinerary(it):
    """Eine Verbindung von Transitous in unserer Form; Zeiten mit der Zeitzone des Orts."""
    legs = []
    for leg in it.get("legs") or []:
        src, dst = leg.get("from") or {}, leg.get("to") or {}
        geometry = leg.get("legGeometry") or {}
        path = decode_polyline(geometry.get("points") or "", int(geometry.get("precision") or 6))
        item = {"from": str(src.get("name") or ""), "to": str(dst.get("name") or ""),
                "from_coord": motis_coord(src), "to_coord": motis_coord(dst),
                "dep_tz": src.get("tz"), "arr_tz": dst.get("tz")}
        mode = leg.get("mode")
        if mode in MOTIS_KINDS:
            live = bool(leg.get("realTime"))
            dep, arr = iso_time(leg.get("scheduledStartTime")), iso_time(leg.get("scheduledEndTime"))
            if dep is None or arr is None:
                return None
            stops = [{"name": str(p.get("name") or ""), "coord": motis_coord(p),
                      "time": iso_time(p.get("scheduledDeparture") or p.get("scheduledArrival")),
                      "real": iso_time(p.get("departure") or p.get("arrival")) if live else None,
                      "cancelled": bool(p.get("cancelled")), "tz": p.get("tz")}
                     for p in leg.get("intermediateStops") or []]
            if len(path) < 2:
                path = [c for c in [item["from_coord"]] + [s["coord"] for s in stops] + [item["to_coord"]] if c]
            dep_pl, dep_new = motis_track(src)
            arr_pl, arr_new = motis_track(dst)
            item.update(type="ride", dep=dep, dep_real=iso_time(leg.get("startTime")) if live else None,
                        arr=arr, arr_real=iso_time(leg.get("endTime")) if live else None,
                        line=motis_line(leg), kind=MOTIS_KINDS[mode], direction=str(leg.get("headsign") or "").strip(),
                        stops=stops, path=path, operator=str(leg.get("agencyName") or ""),
                        cancelled=bool(leg.get("cancelled") or src.get("cancelled") or dst.get("cancelled")),
                        dep_platform=dep_pl, dep_platform_changed=dep_new, arr_platform=arr_pl,
                        arr_platform_changed=arr_new, reachable=True, jid=leg.get("tripId"),
                        rt_source=SOURCE_NAMES["motis"] if live else None)
        else:                                   # zu Fuss (auch beim Umsteigen) oder mit dem Rad
            dep, arr = iso_time(leg.get("startTime")), iso_time(leg.get("endTime"))
            if dep is None or arr is None:
                continue
            meters = leg.get("distance")
            item.update(type="bike" if mode == "BIKE" else "walk", dep=dep, dep_real=None, arr=arr, arr_real=None,
                        duration=float(leg.get("duration") or arr - dep),
                        distance=round(meters) if isinstance(meters, (int, float)) and meters >= 1 else None,
                        path=path if len(path) >= 2 else [c for c in (item["from_coord"], item["to_coord"]) if c])
        legs.append(item)
    if not any(l["type"] == "ride" for l in legs):
        return None
    first, last = legs[0], legs[-1]
    return {"dep": first["dep"], "dep_real": first.get("dep_real"), "arr": last["arr"],
            "arr_real": last.get("arr_real"), "dep_tz": next((l["dep_tz"] for l in legs if l.get("dep_tz")), None),
            "arr_tz": next((l["arr_tz"] for l in reversed(legs) if l.get("arr_tz")), None),
            "changes": max(0, sum(1 for l in legs if l["type"] == "ride") - 1), "legs": legs,
            "cancelled": any(l.get("cancelled") for l in legs), "reachable": True, "planner": "motis"}


def motis_places(text, near=None):
    """Orte in ganz Europa: Haltestellen, Adressen und Ziele (Geocoder von Transitous auf
    OpenStreetMap-Daten). near: Zuhause - Treffer dort in der Naehe kommen zuerst."""
    params = [("text", text), ("language", "de")]
    if near:
        params.append(("place", "%.5f,%.5f" % (near["latitude"], near["longitude"])))
    data = motis("/v1/geocode", params)
    return [p for p in (place_from_match(m) for m in (data if isinstance(data, list) else [])) if p]


def place_from_match(match):
    """Ein Treffer der Transitous-Suche als Ort, mit Stadt und Land darunter."""
    coord = motis_coord(match)
    name = str(match.get("name") or "").strip()
    if not coord or not name:
        return None
    kind = MOTIS_PLACE_TYPES.get(match.get("type"), "C")
    areas = [a for a in match.get("areas") or [] if isinstance(a, dict) and a.get("name")]
    town = next((a["name"] for a in areas if a.get("default")), "")
    country = next((a["name"] for a in areas if a.get("adminLevel") == 2), "")
    if kind == "S":
        kinds = motis_kinds(match.get("modes"))
        sub = " · ".join(x for x in ("Stop", town, ", ".join(KIND_NAMES[k] for k in kinds)) if x)
    else:
        sub = ", ".join(x for x in (" ".join(x for x in (match.get("zip") if kind == "A" else None, town) if x),
                                    country) if x and x != name)
    place = {"name": name, "sub": sub, "lid": None, "type": kind, "latitude": coord[1], "longitude": coord[0],
             "tz": match.get("tz")}
    if kind == "S" and match.get("id"):
        place["motis"] = str(match["id"])
    return place


def motis_nearby(home):
    """Haltestellen um Zuhause bei Transitous, je Name eine (die naechste - ihre Abfahrten
    umfassen alle gleichnamigen Steige), nach Luftlinie."""
    lat, lon = home["latitude"], home["longitude"]
    dlat = NEAR_M / 111320.0
    dlon = dlat / max(0.2, math.cos(math.radians(lat)))
    data = motis("/v6/map/stops", [("min", "%.6f,%.6f" % (lat - dlat, lon - dlon)),
                                   ("max", "%.6f,%.6f" % (lat + dlat, lon + dlon)), ("grouped", "true"),
                                   ("language", "de")])
    best = {}
    for place in data if isinstance(data, list) else []:
        coord, kinds = motis_coord(place), motis_kinds(place.get("modes"))
        if not coord or not kinds or not place.get("stopId"):
            continue                            # Mitfahrboersen und Orte ohne Linien
        meters = distance_m(lat, lon, coord[1], coord[0])
        name = str(place.get("name") or "").strip()
        if meters > NEAR_M or not name:
            continue
        old = best.get(plain_name(name))
        if old is not None:
            kinds = [k for k in KIND_ORDER if k in set(kinds) | set(old["kinds"])]
            if old["distance"] <= meters:
                old["kinds"] = kinds
                continue
        best[plain_name(name)] = {"key": "motis|%s" % place["stopId"], "name": name, "latitude": coord[1],
                                  "longitude": coord[0], "kinds": kinds, "distance": round(meters),
                                  "walk": walk_estimate(meters), "ids": {"motis": str(place["stopId"])},
                                  "serve": ["motis"], "learned": time.time()}
    return sorted(best.values(), key=lambda s: s["distance"])[:NEAR_MAX + 5]


# ------------------------------------------------------------------ Zustaendigkeit

AUSTRIA_RINGS = [[tuple(float(v) for v in point.split(",")) for point in ring.split()] for ring in AUSTRIA_BORDER]
AUSTRIA_BOX = (min(x for r in AUSTRIA_RINGS for x, _y in r), min(y for r in AUSTRIA_RINGS for _x, y in r),
               max(x for r in AUSTRIA_RINGS for x, _y in r), max(y for r in AUSTRIA_RINGS for _x, y in r))


def in_rings(rings, lon, lat):
    """Liegt der Punkt in den Ringen? (Strahlverfahren)"""
    inside = False
    for ring in rings:
        x1, y1 = ring[-1]
        for x2, y2 in ring:
            if (y2 > lat) != (y1 > lat) and lon < (x1 - x2) * (lat - y2) / (y1 - y2) + x2:
                inside = not inside
            x1, y1 = x2, y2
    return inside


def in_austria(lat, lon):
    """Liegt der Ort in Oesterreich (auf rund 1 km genau)? Dort gelten die Schnittstellen
    der Betreiber, sonst Transitous."""
    return in_box(AUSTRIA_BOX, lat, lon) and in_rings(AUSTRIA_RINGS, lon, lat)

def in_box(box, lat, lon):
    return box[0] <= lon <= box[2] and box[1] <= lat <= box[3]


def city_of(lat, lon):
    """Wiener Linien oder Linz AG, wenn der Ort in ihrem Stadtgebiet liegt."""
    return next((src for src, box in CITY_AREAS.items() if in_box(box, lat, lon)), None)


def verbund_of(lat, lon):
    """VOR oder OÖVV - der Verkehrsverbund, in dem der Ort liegt."""
    return next((src for src, box in VERBUND_AREAS.items() if in_box(box, lat, lon)), None)


def owner(item):
    """Wessen Schnittstelle eine Abfahrt oder Etappe liefern soll: die Wiener Linien und
    die Linz AG ihre Linien, die ÖBB Zuege und Postbus, der Verbund alle anderen Busse."""
    op = (item.get("operator") or "").lower()
    if "wiener linien" in op:
        return "wl"
    if "linz linien" in op or "linz ag" in op:
        return "linzag"
    if item.get("kind") == "train" or "öbb" in op or "postbus" in op or "oebb" in op:
        return "oebb"
    return "regional"


# ------------------------------------------------------------------ Orte und Haltestellen

def place_from_loc(loc):
    """Ein Ort aus der HAFAS-Ortssuche: Haltestelle (S), Adresse (A) oder Ziel (P)."""
    coord = hafas_coord(loc)
    name = str(loc.get("name") or "").strip()
    if not name or not coord:
        return None
    kind = loc.get("type") if loc.get("type") in ("S", "A", "P") else "C"
    title, sub = name, ""
    if kind == "A":
        found = re.match(r"^(\d{4,5} [^,]+), (.+)$", name)      # '4040 Linz, Altenberger Straße 69'
        if found:
            title, sub = found.group(2), found.group(1)
    elif kind == "P" and ", " in name:                          # 'JKU Mensa, Altenberger Strasse 69, 4040 Linz'
        title, sub = name.split(", ", 1)
    if kind == "S":
        kinds = kinds_of(loc.get("pCls"))
        sub = "Stop" + (" · " + ", ".join(KIND_NAMES[k] for k in kinds) if kinds else "")
    return {"name": title, "sub": sub, "lid": loc.get("lid"), "type": kind,
            "latitude": coord[1], "longitude": coord[0]}


def oebb_places(text):
    """Orte zu einem Suchtext, wie sie die ÖBB-Auskunft kennt: Haltestellen, Adressen und
    Ziele (Geschaefte, Schulen ...) in ganz Oesterreich."""
    res = hafas_one("oebb", "LocMatch", {"input": {"field": "S", "loc": {"name": text, "type": "ALL"}, "maxLoc": 10}})
    return [p for p in (place_from_loc(loc) for loc in ((res.get("match") or {}).get("locL")) or []) if p]


def folded(text):
    """Zum Vergleichen: klein, ohne Akzente ('München' -> 'munchen')."""
    return "".join(c for c in unicodedata.normalize("NFKD", str(text).casefold()) if not unicodedata.combining(c))


def search_places(text, near=None):
    """Orte zu einem Suchtext: in Oesterreich von der ÖBB-Auskunft, im Rest Europas von
    Transitous (antwortet einer nicht, zaehlt der andere ueberall). Was alle Woerter der
    Suche enthaelt, steht oben; sonst zuerst die Gegend von Zuhause (near)."""
    found = run_parallel({"oebb": lambda: oebb_places(text), "motis": lambda: motis_places(text, near)})
    austria, europe = found.get("oebb"), found.get("motis")
    if not isinstance(austria, list) and not isinstance(europe, list):
        raise next((e for e in (austria, europe) if isinstance(e, Offline)), austria)
    if not isinstance(austria, list):
        log("no places from ÖBB (%s)" % austria)
    if not isinstance(europe, list):
        log("no places from Transitous (%s)" % europe)
    ours = [p for p in austria or [] if not isinstance(europe, list) or in_austria(p["latitude"], p["longitude"])]
    theirs = [p for p in europe or [] if not isinstance(austria, list) or not in_austria(p["latitude"], p["longitude"])]
    abroad = near is not None and not in_austria(near["latitude"], near["longitude"])
    places = theirs + ours if abroad else ours + theirs
    words = [w for w in folded(text).split() if len(w) > 1]
    places.sort(key=lambda p: -sum(1 for w in words if w in folded(p["name"] + " " + p["sub"])))
    out = []
    for place in places:
        if all((p["name"], p["sub"]) != (place["name"], place["sub"]) for p in out):
            out.append(place)
    return out[:12]


def distance_m(lat1, lon1, lat2, lon2):
    a = (math.sin(math.radians(lat2 - lat1) / 2) ** 2 + math.cos(math.radians(lat1))
         * math.cos(math.radians(lat2)) * math.sin(math.radians(lon2 - lon1) / 2) ** 2)
    return 12742000 * math.asin(math.sqrt(min(1.0, a)))


def walk_estimate(meters):
    """Gehzeit in Sekunden ohne Router: Luftlinie mal 1,3 bei WALK_SPEED."""
    return meters * 1.3 / WALK_SPEED * 60


def plain_name(name):
    """Haltestellenname zum Vergleichen zwischen Betreibern: ohne Ort davor, ohne
    Klammerzusatz, ohne Gross-/Kleinschreibung und Satzzeichen."""
    name = re.sub(r"\([^)]*\)", "", str(name or ""))
    name = name.split(",")[-1] if "," in name else name
    words = name.split()
    if len(words) > 1 and ("/" in words[0] or words[0] in ("Wien", "Linz", "Graz", "Salzburg", "Innsbruck")):
        words = words[1:]
    return re.sub(r"[^a-z0-9äöüß]+", "", " ".join(words).lower())


def same_stop_name(a, b):
    """Gleiche Haltestelle bei zwei Betreibern? 'Wien Praterstern Bahnhof (Westseite)'
    bei der ÖBB ist 'Praterstern' bei den Wiener Linien - der eine Name beginnt mit dem
    anderen."""
    a, b = plain_name(a), plain_name(b)
    if not a or not b:
        return False
    short, long_ = sorted((a, b), key=len)
    return a == b or (len(short) >= 5 and long_.startswith(short))


def oebb_nearby(home):
    res = hafas_one("oebb", "LocGeoPos", {"ring": {"cCrd": {"x": round(home["longitude"] * 1e6),
                                                            "y": round(home["latitude"] * 1e6)}, "maxDist": NEAR_M},
                                          "getPOIs": False, "getStops": True, "maxLoc": NEAR_MAX})
    stops = []
    for loc in res.get("locL") or []:
        coord = hafas_coord(loc)
        if loc.get("type") != "S" or not loc.get("lid") or not coord:
            continue
        air = distance_m(home["latitude"], home["longitude"], coord[1], coord[0])
        stops.append({"key": loc["lid"], "name": str(loc.get("name") or ""), "latitude": coord[1],
                      "longitude": coord[0], "kinds": kinds_of(loc.get("pCls")), "distance": round(air),
                      "walk": walk_estimate(air), "ids": {"oebb": loc["lid"]}})
    return stops


def attach_efa(source, stops, home):
    """Die Haltestellen-Nummern von Wiener Linien bzw. Linz AG dazu: gleicher Name, nah
    beieinander. Was nur dieser Betreiber kennt, kommt neu dazu."""
    town = stops[0]["name"].split(" ")[0] + " " if stops and " " in stops[0]["name"] else ""
    for pin in efa_nearby(source, home["latitude"], home["longitude"]):
        lon, lat = pin["coord"]
        # Eine EFA-Haltestelle ist die ganze Station; HAFAS teilt sie oft in Steige
        # ("Hessenplatz (Schubertstraße)", "(Wirtschaftskammer)") - alle bekommen die Nummer.
        matches = [stop for stop in stops if same_stop_name(stop["name"], pin["name"])
                   and distance_m(lat, lon, stop["latitude"], stop["longitude"]) <= MATCH_M]
        for stop in matches:
            stop["ids"].setdefault(source, pin["id"])
        if matches:
            continue
        if pin["distance"] > NEAR_M:
            continue
        air = distance_m(home["latitude"], home["longitude"], lat, lon)
        stops.append({"key": "%s:%s" % (source, pin["id"]), "name": town + pin["name"], "latitude": lat,
                      "longitude": lon, "kinds": pin["kinds"], "distance": round(air), "walk": walk_estimate(air),
                      "ids": {source: pin["id"]}})


def attach_vao(source, stops, home):
    """Die Haltestellen-Kennungen von VOR bzw. OÖVV dazu (gleiche Namen wie bei der ÖBB)."""
    res = hafas_one(source, "LocGeoPos", {"ring": {"cCrd": {"x": round(home["longitude"] * 1e6),
                                                            "y": round(home["latitude"] * 1e6)}, "maxDist": NEAR_M},
                                          "getPOIs": False, "getStops": True, "maxLoc": NEAR_MAX + 10})
    locs = [loc for loc in res.get("locL") or [] if loc.get("type") == "S" and loc.get("lid") and hafas_coord(loc)]
    for stop in stops:                          # gleicher Name (VAO und ÖBB teilen die Daten) ...
        same = next((loc for loc in locs if loc.get("name") == stop["name"]), None)
        if same is None:                        # ... sonst gleich benannt und am naechsten
            near = [(distance_m(hafas_coord(loc)[1], hafas_coord(loc)[0], stop["latitude"], stop["longitude"]), n)
                    for n, loc in enumerate(locs) if same_stop_name(loc.get("name"), stop["name"])]
            near = [x for x in near if x[0] <= MATCH_M]
            same = locs[min(near)[1]] if near else None
        if same is not None:
            stop["ids"].setdefault(source, same["lid"])


def nearby_stops(home):
    """Haltestellen um Zuhause, nach Gehzeit sortiert: in Oesterreich mit den Kennungen
    aller zustaendigen Betreiber, sonst von Transitous. Die Gehzeiten kommen vom
    OSRM-Fussgaenger-Router."""
    lat, lon = home["latitude"], home["longitude"]
    if in_austria(lat, lon):
        stops = oebb_nearby(home)
        jobs = {}
        city, verbund = city_of(lat, lon), verbund_of(lat, lon)
        if city:
            jobs[city] = lambda: attach_efa(city, stops, home)
        if verbund:
            jobs[verbund] = lambda: attach_vao(verbund, stops, home)
        for source, result in run_parallel(jobs).items():   # Betreiber nicht erreichbar - dann ohne ihn
            if isinstance(result, Exception):
                log("no stops from %s (%s)" % (SOURCE_NAMES[source], result))
    else:
        stops = motis_nearby(home)
    try:
        for stop, (secs, meters) in zip(stops, walk_times(home, stops)):
            if secs is not None:
                stop["walk"] = secs
            if meters is not None:
                stop["distance"] = round(meters)
    except (Offline, ServiceError, NoResult, KeyError, TypeError, IndexError) as exc:
        log("no walking times from OSRM (%s) - estimated from the distance" % exc)
    stops.sort(key=lambda s: s["walk"])
    return stops[:NEAR_MAX + 5]


def walk_times(home, stops):
    """[(Sekunden, Meter)] zu Fuss von Zuhause zu jeder Haltestelle, eine OSRM-Anfrage."""
    if not stops:
        return []
    coords = ";".join("%.6f,%.6f" % (p["longitude"], p["latitude"]) for p in [home] + stops)
    data = request_json("%s/routed-foot/table/v1/driving/%s" % (OSRM_URL, coords),
                        params={"sources": "0", "annotations": "duration,distance"})
    if not isinstance(data, dict) or data.get("code") != "Ok":
        raise ServiceError("OSRM table: %s" % (data.get("code") if isinstance(data, dict) else "?"))
    secs = (data.get("durations") or [[]])[0][1:]
    meters = (data.get("distances") or [[]])[0][1:]
    return [(secs[i] if i < len(secs) and isinstance(secs[i], (int, float)) else None,
             meters[i] if i < len(meters) and isinstance(meters[i], (int, float)) else None)
            for i in range(len(stops))]


def default_stops(stops):
    """Vorauswahl: die naechste Haltestelle, dazu eine, die andere Verkehrsmittel hat
    (etwa ein Bahnhof neben der Strassenbahn), hoechstens DEFAULT_WALK entfernt."""
    chosen, kinds = [], set()
    for stop in stops:
        if not chosen or (stop["walk"] <= DEFAULT_WALK and set(stop["kinds"]) - kinds):
            chosen.append(stop)
            kinds |= set(stop["kinds"])
        if len(chosen) == DEFAULT_STOPS:
            break
    return chosen


def town_prefix(names):
    """Der Ortsname vor den Haltestellennamen ('Linz/Donau ', 'Wien '), wenn die meisten
    Haltestellen ihn tragen - im Menue faellt er weg."""
    firsts = [n.split(" ", 1)[0] for n in names if " " in n]
    if not firsts:
        return ""
    best = max(set(firsts), key=firsts.count)
    return best + " " if firsts.count(best) * 2 > len(names) else ""


def short_name(name, prefix):
    """'Linz/Donau Taubenmarkt' -> 'Taubenmarkt' beim Ortsnamen von Zuhause."""
    if prefix and name and name.startswith(prefix) and len(name) > len(prefix):
        return name[len(prefix):]
    return name or ""


def at_stop(dep, stop):
    """Faehrt die Abfahrt an dieser Haltestelle ab (und nicht an einer benachbarten)?
    Gleicher Name - oder ein Teil davon wie 'Linz/Donau Hbf (Busterminal)'."""
    at, name = dep.get("at") or "", stop["name"]
    return at == name or at.startswith(name + " (")


def stop_serves(stop):
    """Wessen Schnittstellen fuer diese Haltestelle gefragt werden (gelernt, sonst geraten)."""
    if stop.get("serve"):
        return list(stop["serve"])
    ids = stop.get("ids") or {}
    if ids.get("motis"):
        return ["motis"]
    guess = [src for src in ("wl", "linzag") if ids.get(src)]
    if ids.get("oebb") and (not guess or "train" in (stop.get("kinds") or [])):
        guess.append("oebb")
    return guess or [next(iter(ids))]           # nur eine Kennung, etwa nur beim VOR


def complete_ids(stop):
    """Kennungen der Betreiber nachtragen, die hier zustaendig sind (Haltestellen aus
    Version 1 kennen nur die ÖBB, oder ein Betreiber war beim Einrichten nicht erreichbar)."""
    lat, lon = stop["latitude"], stop["longitude"]
    if stop["ids"].get("motis"):                # Transitous: eine Kennung genuegt
        return
    place = {"latitude": lat, "longitude": lon}
    city, verbund = city_of(lat, lon), verbund_of(lat, lon)
    if city and city not in stop["ids"]:
        attach_efa(city, [stop], place)
    if verbund and verbund not in stop["ids"]:
        attach_vao(verbund, [stop], place)


def learn_serves(stop, now):
    """Welche Betreiber an der Haltestelle fahren - aus der ÖBB-Tafel der naechsten
    vier Stunden (die kennt alle). -> (Liste der Schnittstellen, sicher?)"""
    if (stop.get("ids") or {}).get("motis"):
        return ["motis"], True                  # ausserhalb Oesterreichs: alles von Transitous
    try:
        complete_ids(stop)
    except (Offline, ServiceError, NoResult, KeyError, TypeError) as exc:
        log("could not complete the stop numbers of %s (%s)" % (stop["name"], exc))
    ids = stop.get("ids") or {}
    owners = set()
    if ids.get("oebb"):
        meth, req = hafas_board("oebb", ids["oebb"], now, 60, {"dur": 240})
        owners = {owner(d) for d in parse_board(hafas_one("oebb", meth, req), "oebb") if at_stop(d, stop)}
    if not owners:
        return stop_serves(dict(stop, serve=None)), False
    verbund = verbund_of(stop["latitude"], stop["longitude"])
    serve = set()
    for who in owners:
        if who in ("wl", "linzag"):
            serve.add(who if ids.get(who) else "oebb")
        elif who == "regional":
            serve.add(verbund if verbund and ids.get(verbund) else "oebb")
        else:
            serve.add("oebb")
    return sorted(serve), True


# ------------------------------------------------------------------ Filter: Linien und Richtungen

# Je Haltestelle (settings["filters"][stop_key]) eine Liste, was Menue und Abfahrten
# weglassen: {"line", "kind"} die ganze Linie, {"line", "kind", "towards": [Ziele],
# "dir"} eine Richtung. Was nicht drinsteht, wird gezeigt - auch neue Linien und Ziele,
# etwa Nachtbusse oder Ersatzverkehr. Die Richtung zaehlt nach der Kennung des
# Betreibers (Wiener Linien, Linz AG und ÖBB-Stadtlinien H/R, Transitous 0/1): so
# gehoeren Kurzfuehrungen dazu. Zuege haben keine, dort zaehlt das Ziel.

def line_key(line):
    """Linie zum Vergleichen: 'REX 8' = 'rex8'."""
    return re.sub(r"\s+", "", str(line or "")).casefold()


def towards_key(text):
    """Ziel zum Vergleichen: 'Ort, Gasse' (Wiener Linien) = 'Ort Gasse' (ÖBB)."""
    return re.sub(r"[^0-9a-z]+", "", folded(text))


def natural(text):
    """Sortierschluessel fuer Linien: '9' vor '11', 'U3' vor 'U6'."""
    return [int(p) if p.isdigit() else p.casefold() for p in re.split(r"(\d+)", str(text))]


def dep_hidden(dep, rules):
    """Laesst der Filter (rules) diese Abfahrt weg?"""
    line = line_key(dep["line"])
    for rule in rules or []:
        if line_key(rule["line"]) != line:
            continue
        if not rule.get("towards"):
            return True                         # die ganze Linie
        if rule.get("dir") and dep.get("dir"):
            if rule["dir"] == dep["dir"]:
                return True
        elif towards_key(dep["direction"]) in {towards_key(t) for t in rule["towards"]}:
            return True
    return False


def same_direction(rule, direction):
    """Meint die Regel diese Richtung (aus line_groups)?"""
    if not rule.get("towards"):
        return False
    if rule.get("dir") and direction.get("dir"):
        return rule["dir"] == direction["dir"]
    return bool({towards_key(t) for t in rule["towards"]} & {towards_key(t) for t in direction["towards"]})


def line_hidden(rules, line):
    return any(line_key(r["line"]) == line_key(line) and not r.get("towards") for r in rules or [])


def direction_hidden(rules, group, direction):
    return line_hidden(rules, group["line"]) or any(
        line_key(r["line"]) == line_key(group["line"]) and same_direction(r, direction) for r in rules or [])


def direction_rule(group, direction):
    rule = {"line": group["line"], "kind": group["kind"], "towards": list(direction["towards"])}
    if direction.get("dir"):
        rule["dir"] = direction["dir"]
    return rule


def toggle_direction(rules, group, direction, show):
    """Die Regeln, wenn eine Richtung an- oder abgehakt wird. Ist danach keine bekannte
    Richtung der Linie mehr an, faellt die ganze Linie weg - auch mit neuen Zielen."""
    key = line_key(group["line"])
    others = [r for r in rules if line_key(r["line"]) != key]
    mine = [r for r in rules if line_key(r["line"]) == key and r.get("towards")]
    if line_hidden(rules, group["line"]):       # war ganz aus: alle Richtungen einzeln aus
        mine = [direction_rule(group, d) for d in group["dirs"]]
    mine = [r for r in mine if not same_direction(r, direction)]
    if not show:
        mine.append(direction_rule(group, direction))
    if group["dirs"] and all(any(same_direction(r, d) for r in mine) for d in group["dirs"]):
        mine = [{"line": group["line"], "kind": group["kind"]}]
    return others + mine


def toggle_line(rules, group, show):
    """Die ganze Linie an (alle ihre Regeln weg) oder aus."""
    key = line_key(group["line"])
    others = [r for r in rules if line_key(r["line"]) != key]
    return others if show else others + [{"line": group["line"], "kind": group["kind"]}]


def line_groups(deps, rules):
    """Linien und Richtungen einer Haltestelle fuer den Filter, aus Abfahrten und Regeln -
    so bleibt auch waehlbar, was ausgeblendet ist und gerade nicht faehrt.
    -> [{"line", "kind", "dirs": [{"dir", "towards": [Ziele, das haeufigste zuerst]}]}],
    Zug vor U-Bahn vor Bim vor Bus, darin nach Nummer."""
    lines = {}

    def add(line, kind, flag, towards, weight):
        group = lines.setdefault(line_key(line), {"line": line, "kind": kind, "dirs": []})
        if not towards:
            return
        key = towards_key(towards)
        for item in group["dirs"]:
            if (item["dir"] == flag) if flag and item["dir"] else key in item["count"]:
                break
        else:
            item = {"dir": None, "count": {}, "name": {}}
            group["dirs"].append(item)
        item["dir"] = item["dir"] or flag
        item["count"][key] = item["count"].get(key, 0) + weight
        item["name"].setdefault(key, towards)

    for dep in deps:
        add(dep["line"], dep["kind"], dep.get("dir"), dep["direction"], 1)
    for rule in rules or []:
        for towards in rule.get("towards") or [None]:
            add(rule["line"], rule.get("kind") or "bus", rule.get("dir"), towards, 0)
    out = []
    for group in lines.values():
        dirs = [{"dir": item["dir"], "towards": [item["name"][k] for k in sorted(item["count"],
                                                                            key=lambda k: -item["count"][k])]}
                for item in group["dirs"]]
        dirs.sort(key=lambda d: folded(d["towards"][0]))
        out.append({"line": group["line"], "kind": group["kind"], "dirs": dirs})
    out.sort(key=lambda g: (KIND_ORDER.index(g["kind"]) if g["kind"] in KIND_ORDER else len(KIND_ORDER),
                            natural(g["line"])))
    return out


def filter_text(rules, prefix=""):
    """'13A, U4 → Hütteldorf' - was der Filter weglaesst."""
    parts = sorted(rules or [], key=lambda r: (natural(r["line"]), folded((r.get("towards") or [""])[0])))
    return ", ".join("%s → %s" % (r["line"], short_name(r["towards"][0], prefix)) if r.get("towards") else r["line"]
                     for r in parts)


def clean_rules(rules):
    """Regeln aus settings.json pruefen."""
    out = []
    for rule in rules if isinstance(rules, list) else []:
        if not isinstance(rule, dict) or not str(rule.get("line") or "").strip():
            continue
        item = {"line": str(rule["line"]).strip(), "kind": rule["kind"] if rule.get("kind") in KIND_ORDER else "bus"}
        towards = rule.get("towards") if isinstance(rule.get("towards"), list) else []
        towards = [str(t) for t in towards if str(t).strip()]
        if towards:
            item["towards"] = towards
            if rule.get("dir"):
                item["dir"] = str(rule["dir"])
        out.append(item)
    return out


def stop_rules(settings, stop):
    return (settings.get("filters") or {}).get(stop_key(stop)) or []


# ------------------------------------------------------------------ Abfahrten

def menu_quota(count):
    """Abfahrtszeilen je Haltestelle: zusammen MENU_ROWS, je Haltestelle mindestens 2."""
    return max(2, MENU_ROWS // max(1, count))


def next_size(table, keep, asked, now, target, least=BOARD_LEAST, most=BOARD_MOST):
    """Wie viele Abfahrten eine Tafel naechstes Mal bringen soll, damit target noch
    kommende dabei sind, die keep zaehlt (bei HAFAS nur die der Haltestelle selbst; was
    der Filter zeigt) - plus ein Viertel Reserve. War sie kuerzer als verlangt, endete
    das Zeitfenster vorher: dann reicht die Groesse."""
    ahead = [k for k, dep in enumerate(table) if keep(dep) and eff_time(dep) >= now]
    mine = sum(1 for dep in table if keep(dep))
    if len(ahead) >= target:
        wanted = (ahead[target - 1] + 1) * 1.25
    elif len(table) < asked:
        wanted = asked
    elif mine:
        wanted = len(table) * (mine - len(ahead) + target) / float(mine) * 1.25
    else:
        wanted = asked * 2
    return max(least, min(most, int(math.ceil(wanted))))


def stop_key(stop):
    return stop.get("key") or (stop.get("ids") or {}).get("oebb") or stop.get("name")


def fetch_departures(stops, now, previous=None, filters=None, survey=False):
    """Die Abfahrten aller gewaehlten Haltestellen, jede Linie von ihrem Betreiber:
    Wiener Linien und Linz AG ihre eigenen, die ÖBB Zuege und Postbus, VOR bzw. OÖVV
    die anderen Busse (diese hoechstens alle POLL_VAO, sie antworten gross). Alle
    Quellen gleichzeitig. Die Tafeln sind so gross, dass genug Abfahrten dabei sind, die
    der Filter zeigt (filters: {stop_key: Regeln}); ist er neu oder geaendert, einmal so
    gross wie erlaubt und ohne Zwischenstand. survey: alle Abfahrten der naechsten
    SURVEY_MIN Minuten - welche Linien hier fahren. -> (Abfahrten je Haltestelle,
    gelernte Tafelgroessen, VAO-Stand, Fehler je Quelle)"""
    previous = previous or {}
    filters = filters or {}
    sizes = dict(previous.get("sizes") or {})
    vao_old = {} if survey else previous.get("vao") or {}
    quota = menu_quota(len(stops)) + BOARD_SPARE
    serves = [set(stop_serves(s)) for s in stops]
    rules = [filters.get(stop_key(s)) or [] for s in stops]
    applied = previous.get("filters") or {}
    wide = [r != (applied.get(stop_key(s)) or []) for s, r in zip(stops, rules)]
    jobs, vao_new, asked = {}, {}, {}
    boards_by = {"oebb": {}, "vor": {}, "ooevv": {}, "motis": {}}
    for source in ("oebb", "vor", "ooevv"):
        wanted = []
        for stop, serve, broad in zip(stops, serves, wide):
            lid = (stop.get("ids") or {}).get(source)
            if source not in serve or not lid:
                continue
            key = "%s|%s" % (source, lid)
            if source != "oebb":                # gross und ungepackt: wie bisher, auch mit Filter
                old = vao_old.get(key)
                if old and now - old.get("at", 0) < POLL_VAO:
                    vao_new[key] = old
                    boards_by[source][stop_key(stop)] = old.get("deps") or []
                    continue
                asked[key] = BOARD_MOST if survey else sizes.get(key, BOARD_START)
            else:
                asked[key] = SURVEY_JNY if survey else BOARD_WIDE if broad else sizes.get(key, BOARD_START)
            wanted.append((stop, key, lid))
        if wanted:
            extra = {"dur": SURVEY_MIN + BOARD_BEFORE // 60} if survey else None
            calls = [hafas_board(source, lid, now, asked[key], extra) for _stop, key, lid in wanted]
            jobs[source] = (lambda src=source, c=calls: hafas(src, *c))
            boards_by[source + "_wanted"] = wanted
    divas = sorted({s["ids"]["wl"] for s, sv in zip(stops, serves) if "wl" in sv and s["ids"].get("wl")})
    if divas:
        jobs["wl"] = lambda: wl_departures(divas, now)
    for stop, serve, broad in zip(stops, serves, wide):
        sid = (stop.get("ids") or {}).get("linzag")
        if "linzag" in serve and sid:
            key = "linzag|" + sid
            size = SURVEY_EFA if survey else EFA_MOST if broad else sizes.get(key, EFA_LIMIT)
            asked[key] = max(asked.get(key, 0), size)    # zwei Steige, eine Linz-AG-Haltestelle
            jobs[key] = (lambda sid=sid, key=key: efa_departures("linzag", sid, now, asked[key]))
        sid = (stop.get("ids") or {}).get("motis")
        if "motis" in serve and sid:
            key = "motis|" + sid
            old = vao_old.get(key)
            if old and not broad and now - old.get("at", 0) < POLL_MOTIS:
                vao_new[key] = old
                boards_by["motis"][stop_key(stop)] = old.get("deps") or []
            else:
                asked[key] = SURVEY_MOTIS if survey else MOTIS_MOST if broad else sizes.get(key, MOTIS_LIMIT)
                jobs[key] = (lambda sid=sid, n=asked[key]: motis_departures(sid, now, n))
    results = run_parallel(jobs)

    def counted(rule, base=None):
        """Was fuer die Groesse einer Tafel zaehlt: was der Filter zeigt (und base zulaesst)."""
        return lambda dep: (base is None or base(dep)) and not dep_hidden(dep, rule)

    errors = {}
    for source in ("oebb", "vor", "ooevv"):
        if source not in results:
            continue
        answer = results[source]
        if isinstance(answer, Exception):
            errors[source] = answer
            continue
        for (stop, key, lid), res in zip(boards_by[source + "_wanted"], answer):
            if isinstance(res, NoResult):
                table = []
            elif isinstance(res, Exception):
                errors[source] = res
                continue
            else:
                table = parse_board(res, source)
                rule = filters.get(stop_key(stop)) or []
                sizes[key] = next_size(table, counted(rule, lambda d, s=stop: at_stop(d, s)), asked[key], now,
                                       quota, most=BOARD_WIDE if rule and source == "oebb" else BOARD_MOST)
            boards_by[source][stop_key(stop)] = table
            if source != "oebb":
                vao_new[key] = {"at": now, "deps": [d for d in table if at_stop(d, stop)]}
    wl = results.get("wl")
    if isinstance(wl, Exception):
        errors["wl"] = wl
    linz, learned = {}, {}
    for name, answer in results.items():
        if name.startswith("linzag|"):
            if isinstance(answer, Exception):
                errors["linzag"] = answer
            else:
                linz[name.split("|", 1)[1]] = answer
                for stop in stops:
                    if "linzag|" + str((stop.get("ids") or {}).get("linzag")) == name:
                        rule = filters.get(stop_key(stop)) or []
                        size = next_size(answer, counted(rule, lambda d: owner(d) == "linzag"), asked[name],
                                         now, quota, EFA_LIMIT, EFA_MOST if rule else EFA_LIMIT)
                        learned[name] = max(learned.get(name, 0), size)
        elif name.startswith("motis|"):
            if isinstance(answer, Exception) and not isinstance(answer, NoResult):
                errors["motis"] = answer
            else:
                deps = [] if isinstance(answer, Exception) else answer
                vao_new[name] = {"at": now, "deps": deps}
                for stop in stops:
                    if "motis|" + str((stop.get("ids") or {}).get("motis")) == name:
                        boards_by["motis"][stop_key(stop)] = deps
                        rule = filters.get(stop_key(stop)) or []
                        learned[name] = next_size(deps, counted(rule), asked[name], now, quota,
                                                  MOTIS_LIMIT, MOTIS_MOST if rule else MOTIS_LIMIT)
    sizes.update(learned)

    boards = []
    for stop, serve in zip(stops, serves):
        ids, key = stop.get("ids") or {}, stop_key(stop)
        deps, missing = [], False
        if "wl" in serve:
            if isinstance(wl, dict):
                deps += wl.get(str(ids.get("wl")), [])
            else:
                missing = True
        if "linzag" in serve:
            if ids.get("linzag") in linz:
                deps += [d for d in linz[ids["linzag"]] if owner(d) == "linzag"]
            else:
                missing = True
        if "oebb" in serve:
            table = boards_by["oebb"].get(key)
            if table is None:
                missing = True
            else:
                deps += [d for d in table if at_stop(d, stop) and from_oebb(d, serve)]
        for source in ("vor", "ooevv"):
            if source in serve:
                table = boards_by[source].get(key)
                if table is None:
                    missing = True
                else:
                    deps += [d for d in table if at_stop(d, stop) and owner(d) == "regional"]
        if "motis" in serve:
            table = boards_by["motis"].get(key)
            if table is None:
                missing = True
            else:
                deps += table
        seen, merged = set(), []
        for dep in sorted(deps, key=lambda d: (eff_time(d), d["line"])):
            mark = (dep["line"].lower(), int(dep["planned"] // 60), plain_name(dep["direction"])[:6])
            if mark not in seen:
                seen.add(mark)
                merged.append(dep)
        boards.append(merged if merged or not missing else None)
    return boards, sizes, vao_new, errors


def from_oebb(dep, serve):
    """Kommt diese Abfahrt von der ÖBB? Ja fuer Zuege und Postbus - und fuer alles,
    dessen Betreiber hier keine eigene Schnittstelle hat."""
    who = owner(dep)
    return who == "oebb" or (who in ("wl", "linzag") and who not in serve) \
        or (who == "regional" and not ({"vor", "ooevv"} & set(serve)))


def fetch_state(settings, now, previous=None):
    """(Cache-Eintrag oder None, Zustand, Detail). Zustand: ok, offline, error. Fehlt
    nur eine Quelle, ist es "ok" - ihre Haltestellen zeigen dann den letzten Stand."""
    stops = settings.get("stops") or []
    filters = settings.get("filters") or {}
    try:
        boards, sizes, vao, errors = fetch_departures(stops, now, previous, filters)
    except Offline as exc:
        return None, "offline", str(exc)
    except Exception as exc:  # noqa: BLE001 - das Widget soll weiterlaufen
        return None, "error", "%s: %s" % (type(exc).__name__, exc)
    if errors and all(b is None for b in boards):
        first = next(iter(errors.values()))
        return None, ("offline" if isinstance(first, Offline) else "error"), "; ".join(
            "%s: %s" % (SOURCE_NAMES.get(k, k), v) for k, v in errors.items())
    old = (previous or {}).get("boards") or []
    for i, board in enumerate(boards):         # Quelle fehlt: deren Haltestelle mit dem letzten Stand
        if board is None and i < len(old):
            boards[i] = old[i]
    detail = "; ".join("%s: %s" % (SOURCE_NAMES.get(k, k), v) for k, v in errors.items()) or None
    # Mit welchem Filter die Tafelgroessen gelernt sind - ein neuer fragt einmal breit
    applied = {stop_key(s): filters[stop_key(s)] for s in stops if filters.get(stop_key(s))}
    return {"fetched_at": time.time(), "stops": [stop_key(s) for s in stops], "boards": boards,
            "sizes": sizes, "vao": vao, "filters": applied, "missing": sorted(errors)}, "ok", detail


def survey_lines(stop, now):
    """Alle Abfahrten der naechsten SURVEY_MIN Minuten an einer Haltestelle, von denselben
    Schnittstellen wie im Menue: welche Linien hier in welche Richtungen fahren (fuer den
    Filter). -> (Abfahrten, Betreiber ohne Antwort)"""
    boards, _sizes, _vao, errors = fetch_departures([stop], now, survey=True)
    if boards[0] is None:
        raise next(iter(errors.values()), NoResult("No departures known."))
    return boards[0], sorted(errors)


# ------------------------------------------------------------------ Verbindungen

def hafas_place(place):
    """Ort fuer die HAFAS-Verbindungssuche: Haltestelle, Adresse oder Ziel ueber ihre
    Kennung (nur bei der ÖBB, von deren Ortssuche sie stammt), sonst Koordinaten."""
    if place.get("lid") and place.get("type") in ("S", "A", "P"):
        return {"lid": place["lid"], "type": place["type"]}
    return {"type": "C", "name": place.get("name") or "Place",
            "crd": {"x": round(place["longitude"] * 1e6), "y": round(place["latitude"] * 1e6)}}


def parse_connection(con, common, source):
    """Eine Verbindung: Abfahrt und Ankunft (planmaessig und tatsaechlich), Umstiege und
    die Etappen - Fahrten mit Linie, Richtung, Betreiber, Zwischenhalten und Strecke,
    Fusswege mit Dauer."""
    locs, prods = common.get("locL") or [], common.get("prodL") or []
    date = con.get("date")
    legs = []
    for sec in con.get("secL") or []:
        dep, arr = sec.get("dep") or {}, sec.get("arr") or {}
        start, end = pick(locs, dep.get("locX")), pick(locs, arr.get("locX"))
        leg = {"from": start.get("name") or "", "to": end.get("name") or "",
               "from_coord": hafas_coord(start), "to_coord": hafas_coord(end),
               "dep": hafas_time(date, dep.get("dTimeS"), dep.get("dTZOffset")),
               "dep_real": hafas_time(date, dep.get("dTimeR"), dep.get("dTZOffset")),
               "arr": hafas_time(date, arr.get("aTimeS"), arr.get("aTZOffset")),
               "arr_real": hafas_time(date, arr.get("aTimeR"), arr.get("aTZOffset"))}
        if leg["dep"] is None or leg["arr"] is None:
            continue
        if sec.get("type") == "JNY":
            jny = sec.get("jny") or {}
            prod = pick(prods, jny.get("prodX"))
            kind = product_kind(prod, common)
            stops = []
            for st in (jny.get("stopL") or [])[1:-1]:
                prefix = "d" if st.get("dTimeS") else "a"
                offset = st.get(prefix + "TZOffset")
                loc = pick(locs, st.get("locX"))
                stops.append({"name": loc.get("name") or "", "coord": hafas_coord(loc),
                              "time": hafas_time(date, st.get(prefix + "TimeS"), offset),
                              "real": hafas_time(date, st.get(prefix + "TimeR"), offset),
                              "cancelled": bool(st.get("dCncl") or st.get("aCncl"))})
            dep_pl, dep_new = platform(dep, "d")
            arr_pl, arr_new = platform(arr, "a")
            path = hafas_path(common, jny)
            if len(path) < 2:                   # ohne Strecke: durch die Halte
                path = [c for c in [leg["from_coord"]] + [s["coord"] for s in stops] + [leg["to_coord"]] if c]
            leg.update(type="ride", line=line_label(prod, kind), kind=kind,
                       direction=str(jny.get("dirTxt") or "").strip(), stops=stops, path=path,
                       operator=operator_of(prod, common),
                       cancelled=bool(dep.get("dCncl") or arr.get("aCncl") or jny.get("isCncl")),
                       dep_platform=dep_new or dep_pl, dep_platform_changed=bool(dep_new),
                       arr_platform=arr_new or arr_pl, arr_platform_changed=bool(arr_new),
                       reachable=jny.get("isRchbl", True) is not False, jid=jny.get("jid"),
                       rt_source=SOURCE_NAMES[source] if leg["dep_real"] is not None else None)
        else:                                   # WALK, TRSF und Verwandte: zu Fuss
            gis = sec.get("gis") or {}
            path = hafas_path(common, gis)
            leg.update(type="walk", distance=gis.get("dist"),
                       duration=hafas_seconds(gis.get("durS")) or leg["arr"] - leg["dep"],
                       path=path if len(path) >= 2 else [c for c in (leg["from_coord"], leg["to_coord"]) if c])
        legs.append(leg)
    if not legs:
        return None
    first, last = legs[0], legs[-1]
    return {"dep": first["dep"], "dep_real": first.get("dep_real"), "arr": last["arr"],
            "arr_real": last.get("arr_real"), "changes": con.get("chg") or 0, "legs": legs,
            "cancelled": any(l.get("cancelled") for l in legs),
            "reachable": all(l.get("reachable", True) for l in legs), "planner": source}


def hafas_trips(source, origin, destination, moment, arrive, context=None):
    local = dt.datetime.fromtimestamp(moment, VIENNA)
    req = {"depLocL": [hafas_place(origin) if source == "oebb" else coord_place(origin)],
           "arrLocL": [hafas_place(destination) if source == "oebb" else coord_place(destination)],
           "outDate": local.strftime("%Y%m%d"), "outTime": local.strftime("%H%M%S"), "outFrwd": not arrive,
           "numF": TRIPS, "getPasslist": True, "getPolyline": True}
    if context:
        req["ctxScr"] = context
    res = hafas_one(source, "TripSearch", req)
    common = res.get("common") or {}
    cons = [c for c in (parse_connection(c, common, source) for c in res.get("outConL") or []) if c]
    if not cons:
        raise NoResult("No connections found.")
    return cons, res.get("outCtxScrF"), res.get("outCtxScrB")


def coord_place(place):
    return {"type": "C", "name": place.get("name") or "Place",
            "crd": {"x": round(place["longitude"] * 1e6), "y": round(place["latitude"] * 1e6)}}


def choose_planner(origin, destination):
    """Wer die Verbindung rechnet: liegen Start und Ziel in derselben Stadt, ihr Planer
    (CITY_PLANNERS: in Wien die VAO wie in der WienMobil-App, in Linz die Linz AG), im
    selben Verbund VOR bzw. OÖVV, sonst in Oesterreich die ÖBB - und alles ausserhalb oder
    ueber die Grenze Transitous."""
    if not (in_austria(origin["latitude"], origin["longitude"])
            and in_austria(destination["latitude"], destination["longitude"])):
        return "motis"
    a = city_of(origin["latitude"], origin["longitude"])
    if a and a == city_of(destination["latitude"], destination["longitude"]):
        return CITY_PLANNERS[a]
    v = verbund_of(origin["latitude"], origin["longitude"])
    if v and v == verbund_of(destination["latitude"], destination["longitude"]):
        return v
    return "oebb"


def transit_search(origin, destination, when=None, context=None, planner=None):
    """Verbindungen mit dem zustaendigen Planer; scheitert er, rechnet die ÖBB.
    when: (Zeit, Ankunft?) oder None fuer jetzt. context: Blaettern (vom Ergebnis).
    -> {"cons", "later", "earlier", "planner"}"""
    planner = planner or choose_planner(origin, destination)
    moment, arrive = when if when else (time.time(), False)
    try:
        if planner in EFA_SOURCES or planner == "motis":
            if context:                         # Blaettern: neue Suche ab dem Rand der Liste
                moment, arrive = context
            if planner == "motis":
                cons = motis_trips(origin, destination, moment, arrive)
            else:
                cons = efa_trips(planner, origin, destination, moment, arrive)
            later = (max(c["dep"] for c in cons) + 60, False)
            earlier = (min(c["arr"] for c in cons) - 60, True)
        else:
            cons, later, earlier = hafas_trips(planner, origin, destination, moment, arrive, context)
    except (ServiceError, NoResult) as exc:
        if planner == "oebb" or context:
            raise
        log("%s planner failed (%s) - asking ÖBB" % (SOURCE_NAMES[planner], exc))
        return transit_search(origin, destination, when, None, "oebb")
    enrich_realtime(cons, planner, time.time())
    return {"cons": cons, "later": later, "earlier": earlier, "planner": planner}


def mixed_search(origin, destination, when=None):
    """Rad + Oeffis (Bike & Ride): mit dem eigenen Rad zu einer Haltestelle, dort parken,
    weiter mit Oeffis. Welche Haltestelle sich lohnt, rechnet Transitous (die Planer der
    Betreiber koennen das nicht) - Rad hoechstens MIXED_BIKE_MAX, dazu die Dauer der
    ganzen Strecke mit dem Rad. -> {"cons", "bike" (Sekunden oder None), "planner"}"""
    if distance_m(origin["latitude"], origin["longitude"],
                  destination["latitude"], destination["longitude"]) < MIXED_NEAR_M:
        raise NoResult("This close, cycling all the way is quicker.")
    moment, arrive = when if when else (time.time(), False)
    data = motis("/v6/plan", [("fromPlace", motis_point(origin)), ("toPlace", motis_point(destination)),
                              ("time", motis_utc(moment)), ("arriveBy", "true" if arrive else "false"),
                              ("preTransitModes", "BIKE"), ("maxPreTransitTime", str(MIXED_BIKE_MAX)),
                              ("directModes", "BIKE"), ("numItineraries", str(TRIPS)),
                              ("maxItineraries", str(TRIPS + 3)), ("language", "de")])
    data = data if isinstance(data, dict) else {}
    cons = [c for c in (parse_motis_itinerary(it) for it in data.get("itineraries") or []) if c and cycled(c)]
    direct = [it.get("duration") for it in data.get("direct") or []
              if isinstance(it, dict) and isinstance(it.get("duration"), (int, float))]
    if not cons:
        raise NoResult("No connection with bike and transit found.")
    enrich_realtime(cons, "motis", time.time())
    return {"cons": cons, "bike": float(min(direct)) if direct else None, "planner": "motis"}


_STOP_IDS = {}


def operator_stop(source, leg):
    """Die Haltestellen-Nummer bei Wiener Linien bzw. Linz AG fuer den Einstieg einer
    Etappe: gleicher Name in der Naehe (gemerkt)."""
    coord = leg.get("from_coord")
    if not coord:
        return None
    key = (source, round(coord[0], 4), round(coord[1], 4))
    if key not in _STOP_IDS:
        _STOP_IDS[key] = next((p["id"] for p in efa_nearby(source, coord[1], coord[0], 300, 8)
                               if same_stop_name(p["name"], leg["from"])), None)
    return _STOP_IDS[key]


def enrich_realtime(cons, planner, now):
    """Echtzeit vom Betreiber nachholen, wo ein anderer Planer gerechnet hat: Linien der
    Wiener Linien und der Linz AG bekommen ihre Abfahrtszeit aus deren Schnittstelle
    (ENRICH_LEGS Abfahrten der naechsten zwei Stunden, zuerst die erste Fahrt jeder
    Verbindung - nach ihr richtet sich, wann man los muss. Dieselbe Abfahrt in mehreren
    Verbindungen, oft die U-Bahn am Anfang, zaehlt einmal.)"""
    todo = {}               # Abfahrt -> [fruehester Platz in einer Verbindung, [(Verbindung, Etappe)]]
    for con in cons:
        rank = 0
        for i, leg in enumerate(con["legs"]):
            if leg["type"] != "ride":
                continue
            who = owner(leg)
            # nachholen, wo die Echtzeit nicht schon vom Betreiber selbst kommt
            if who in EFA_SOURCES and leg.get("rt_source") != SOURCE_NAMES[who] \
                    and now - 600 <= leg["dep"] <= now + 7200:
                entry = todo.setdefault((who, leg["from"], leg.get("line"), leg["dep"]), [rank, []])
                entry[0] = min(entry[0], rank)
                entry[1].append((con, i))
            rank += 1
    keys = sorted(todo, key=lambda k: todo[k][0])[:ENRICH_LEGS]
    jobs = {n: (lambda w=key[0], c=todo[key][1][0]: operator_departure(w, c[0]["legs"][c[1]], now))
            for n, key in enumerate(keys)}
    for n, found in run_parallel(jobs).items():
        who = keys[n][0]
        if isinstance(found, Exception):
            log("no real-time from %s (%s)" % (SOURCE_NAMES[who], found))
        elif isinstance(found, dict):
            for con, i in todo[keys[n]][1]:
                leg = con["legs"][i]
                leg["rt_source"] = SOURCE_NAMES[who]
                if found.get("real") is not None:
                    leg["dep_real"] = found["real"]
                    carry_delay(con, i, found["real"] - leg["dep"])
                if found.get("cancelled"):
                    leg["cancelled"] = True
    for con in cons:
        con["cancelled"] = any(l.get("cancelled") for l in con["legs"])


def carry_delay(con, index, delay):
    """Die nachgeholte Verspaetung einer Abfahrt weitertragen, wo der Planer keine Echtzeit
    hat: an die Halte und die Ankunft dieser Fahrt und an die Fusswege danach bis zur
    naechsten Fahrt - kommt keine mehr, an die Ankunft der Verbindung. Sonst fuehre die
    U-Bahn mit +5 um 11:05 ab und kaeme um 11:04 an."""
    legs = con["legs"]
    leg = legs[index]
    for stop in leg.get("stops") or []:
        if stop.get("real") is None and stop.get("time") is not None:
            stop["real"] = stop["time"] + delay
    if leg.get("arr_real") is None:
        leg["arr_real"] = leg["arr"] + delay
    if index == 0:
        con["dep_real"] = leg["dep_real"]
    j = index + 1
    while j < len(legs) and legs[j]["type"] != "ride":
        for key in ("dep", "arr"):
            if legs[j].get(key + "_real") is None:
                legs[j][key + "_real"] = legs[j][key] + delay
        j += 1
    if j == len(legs):
        con["arr_real"] = legs[-1]["arr_real"]


def towards_same(a, b):
    """Dasselbe Fahrtziel bei zwei Auskuenften? 'Wien Kaiserebersdorf, Zinnergasse' bei der
    VAO heisst bei den Wiener Linien etwa 'Kaiserebersdorf, Zinnergasse' oder 'Zinnergasse':
    ein Teil des einen Namens steckt im anderen."""
    def parts(name):
        name = re.sub(r"\([^)]*\)", "", str(name or ""))
        return [p for p in (plain_name(part) for part in name.split(",")) if len(p) >= 4]
    return any(x in y or y in x for x in parts(a) for y in parts(b))


def operator_departure(source, leg, now):
    """Die Abfahrt einer Etappe beim Betreiber: gleiche Linie in dieselbe Richtung (wo
    beide ein Ziel nennen - an der U-Bahn faehrt die Gegenrichtung oft zur selben Minute),
    planmaessig hoechstens 90 Sekunden daneben."""
    stop = operator_stop(source, leg)
    if not stop:
        return None
    deps = wl_departures([stop], now).get(str(stop), []) if source == "wl" else efa_departures(source, stop, now, 40)
    best = None
    for dep in deps:
        if line_key(dep["line"]) != line_key(leg.get("line")) or abs(dep["planned"] - leg["dep"]) > 90:
            continue
        if dep.get("direction") and leg.get("direction") and not towards_same(dep["direction"], leg["direction"]):
            continue
        if best is None or abs(dep["planned"] - leg["dep"]) < abs(best["planned"] - leg["dep"]):
            best = dep
    return best


def con_key(con):
    return tuple((l["type"], l.get("line"), l["dep"]) for l in con["legs"])


def con_duration(con):
    return eff_time(con, "arr") - eff_time(con, "dep")


def walked(con):
    """Sekunden zu Fuss in einer Verbindung, auch beim Umsteigen."""
    return sum(l.get("duration") or 0 for l in con["legs"] if l["type"] == "walk")


def cycled(con):
    """Sekunden mit dem Rad in einer Verbindung."""
    return sum(l.get("duration") or 0 for l in con["legs"] if l["type"] == "bike")


def effort(con):
    """Wie aufwendig eine Verbindung ist: ihre Dauer, je Umstieg CHANGE_COST dazu, Fussweg
    und Rad zu EFFORT_FACTOR - so waegt ein Mensch zwei aehnliche Verbindungen ab."""
    return con_duration(con) + CHANGE_COST * con["changes"] + EFFORT_FACTOR * (walked(con) + cycled(con))


def usable(con):
    return not con["cancelled"] and con["reachable"]


def outdone(con, other):
    """Ist other die sinnvollere Wahl als con? Nie, wenn other frueher losgeht: Wer sie
    knapp verpasst, braucht con (und schon abgefahrene verdraengen so keine, die man noch
    erreicht). Sonst ja, wenn other nicht spaeter ankommt, ohne mehr Umstiege und ohne viel
    mehr Fussweg (MORE_ON_FOOT) - oder hoechstens LATER_SLACK (bzw. LATER_SLACK_WAIT)
    spaeter ankommt und klar weniger Aufwand ist. So fallen weg: 20 Minuten frueher los,
    um 3 Minuten frueher da zu sein; ein Umstieg mehr fuer eine Minute; 25 Minuten
    Fussweg statt der Bim."""
    if other is con or not usable(other):
        return False
    dep, arr = eff_time(con, "dep"), eff_time(con, "arr")
    o_dep, o_arr = eff_time(other, "dep"), eff_time(other, "arr")
    if o_dep < dep:
        return False
    # ohne die Grenze beim Fussweg schloessen sich zwei Verbindungen gegenseitig aus: eine
    # Minute frueher da, aber eine Viertelstunde mehr zu Fuss - und umgekehrt der Aufwand
    if o_arr <= arr and other["changes"] <= con["changes"] \
            and walked(other) + cycled(other) <= walked(con) + cycled(con) + MORE_ON_FOOT \
            and (o_dep > dep or o_arr < arr or other["changes"] < con["changes"]):
        return True
    slack = LATER_SLACK_WAIT if o_dep - dep >= WAIT_GAIN else LATER_SLACK
    return o_arr <= arr + slack and effort(other) + BETTER_BY <= effort(con)


def walk_instead(con, walk):
    """Geht man besser gleich den ganzen Weg zu Fuss (walk: Sekunden)? Ja, wenn die
    Verbindung hoechstens WALK_GAIN schneller ist und dabei kaum Fussweg spart."""
    return con_duration(con) > walk - WALK_GAIN and walk - walked(con) < max(WALK_SAVE, WALK_SAVE_SHARE * walk)


def sensible(cons, walk=None):
    """Nur die sinnvollen Verbindungen, nach Abfahrt sortiert: ohne doppelte, ohne
    ausgefallene und nicht erreichbare (solange es andere gibt), ohne die, zu denen es
    eine klar bessere gibt (outdone), und ohne die, fuer die man genauso gut zu Fuss geht
    (walk: Sekunden fuer den ganzen Weg oder None). -> (Verbindungen, Hinweis oder None)"""
    unique = list({con_key(c): c for c in cons}.values())
    pool = [c for c in unique if usable(c)] or unique
    keep = [c for c in pool if not any(outdone(c, o) for o in pool)]
    if pool and not keep:               # sortieren sie sich doch reihum aus: die mit dem wenigsten Aufwand
        keep = [min(pool, key=effort)]
    if walk and keep and all(walk_instead(c, walk) for c in keep):
        quick = "quicker" if walk <= min(con_duration(c) for c in keep) else "about as quick"
        return [], "Walking is %s (%s) - no need for transit." % (quick, duration_text(walk))
    if walk:
        keep = [c for c in keep if not walk_instead(c, walk)]
    return sorted(keep, key=lambda c: (eff_time(c, "dep"), eff_time(c, "arr"))), None


def sensible_mixed(cons, transit=None, bike=None):
    """Rad + Oeffis nur, wo es sich lohnt: mindestens MIXED_BIKE_MIN mit dem Rad (sonst
    geht man zur Haltestelle) und klar schneller (MIXED_GAIN bzw. MIXED_GAIN_SHARE) als
    die ganze Strecke mit dem Rad und als die schnellste sinnvolle Verbindung nur mit
    Oeffis. bike, transit: deren Dauer in Sekunden oder None. -> (Verbindungen, Hinweis)"""
    keep, _note = sensible([c for c in cons if cycled(c) >= MIXED_BIKE_MIN])
    if not keep:
        return [], "The bike would only take you to a stop around the corner - walk there instead."
    best = min(con_duration(c) for c in keep)
    for base, what in ((bike, "Cycling all the way"), (transit, "Transit alone")):
        if base is None:
            continue
        keep = [c for c in keep if con_duration(c) <= base - max(MIXED_GAIN, MIXED_GAIN_SHARE * base)]
        if not keep:
            return [], "%s is %s (%s)." % (what, "quicker" if base <= best else "about as quick",
                                           duration_text(base))
    return keep, None


def journey_details(source, jid):
    """Alle Halte einer Fahrt mit Zeiten und Strecke."""
    res = hafas_one(source, "JourneyDetails", {"jid": jid, "getPolyline": True})
    common = res.get("common") or {}
    locs = common.get("locL") or []
    jny = res.get("journey") or {}
    date = jny.get("date")
    stops = []
    for st in jny.get("stopL") or []:
        plat, plat_new = platform(st, "d")
        loc = pick(locs, st.get("locX"))
        stops.append({"name": loc.get("name") or "", "coord": hafas_coord(loc),
                      "arr": hafas_time(date, st.get("aTimeS"), st.get("aTZOffset")),
                      "arr_real": hafas_time(date, st.get("aTimeR"), st.get("aTZOffset")),
                      "dep": hafas_time(date, st.get("dTimeS"), st.get("dTZOffset")),
                      "dep_real": hafas_time(date, st.get("dTimeR"), st.get("dTZOffset")),
                      "cancelled": bool(st.get("aCncl") or st.get("dCncl")), "platform": plat_new or plat})
    if not stops:
        raise NoResult("No stops known for this trip.")
    path = hafas_path(common, jny)
    return {"direction": str(jny.get("dirTxt") or ""), "stops": stops,
            "path": path if len(path) >= 2 else [s["coord"] for s in stops if s["coord"]]}


def departure_trip(dep, stop):
    """Der Verlauf einer Abfahrt. Abfahrten von Wiener Linien und Linz AG haben keine
    HAFAS-Kennung: die gleiche Fahrt (Linie, Zeit) wird auf der ÖBB-Tafel gesucht -
    deren Halte und Strecke, die Abfahrtszeit des Betreibers."""
    if dep.get("jid") and dep.get("source") in HAFAS_SOURCES:
        return journey_details(dep["source"], dep["jid"])
    if dep.get("jid") and dep.get("source") == "motis":
        return motis_trip(dep["jid"])
    lid = ((stop or {}).get("ids") or {}).get("oebb")
    if not lid:
        raise NoResult("No stop list known for this departure.")
    meth, req = hafas_board("oebb", lid, dep["planned"] + BOARD_BEFORE - 120, 40, {"dur": 8})
    for cand in parse_board(hafas_one("oebb", meth, req), "oebb"):
        if cand["line"].lower() == dep["line"].lower() and abs(cand["planned"] - dep["planned"]) <= 90 \
                and cand.get("jid"):
            return journey_details("oebb", cand["jid"])
    raise NoResult("No stop list known for this departure.")


# ------------------------------------------------------------------ Rad, zu Fuss, Auto

TURNS = {"left": "Turn left", "right": "Turn right", "slight left": "Bear left", "slight right": "Bear right",
         "sharp left": "Sharp left", "sharp right": "Sharp right", "straight": "Straight on", "uturn": "Turn around"}
TRAFFIC_WORDS = {"JAM": "Traffic jam", "ROAD_WORK": "Roadworks", "ROAD_CLOSURE": "Road closed", "OTHER": "Slow traffic"}


def turn_text(maneuver):
    kind, modifier = maneuver.get("type"), maneuver.get("modifier") or ""
    if kind == "depart":
        return "Start"
    if kind in ("roundabout", "rotary", "roundabout turn", "exit roundabout", "exit rotary"):
        return "Roundabout, exit %d" % maneuver["exit"] if maneuver.get("exit") else "Roundabout"
    if kind == "fork":
        return "Keep " + ("left" if "left" in modifier else "right" if "right" in modifier else "straight on")
    if kind in ("new name", "continue", "notification") and modifier in ("straight", ""):
        return "Continue"
    return TURNS.get(modifier, "Continue")


def condense_steps(steps, mode):
    """Die Abbiegeschritte von OSRM, zusammengefasst: aufeinanderfolgende Stuecke
    derselben Strasse in einem, kurze namenlose Stuecke im vorigen."""
    unnamed = {"bike": "Cycle path", "walk": "Footpath", "car": "Road"}[mode]
    out = []
    for step in steps:
        maneuver = step.get("maneuver") or {}
        if maneuver.get("type") == "arrive":
            continue
        ref = (step.get("ref") or "").split(";")[0].strip()
        name = (step.get("name") or "").strip() or ref
        meters = step.get("distance") or 0
        if out and (not name and meters < 150 or (name or unnamed) == out[-1]["name"]):
            out[-1]["distance"] += meters
            continue
        # road: kurz fuer "via" - die Strassennummer (A 23), wo es eine gibt
        out.append({"name": name or unnamed, "road": ref or name, "turn": turn_text(maneuver), "distance": meters})
    while len(out) > 1 and out[0]["distance"] < 40:     # ein paar Meter bis zur ersten Strasse
        out[1].update(distance=out[1]["distance"] + out[0]["distance"], turn="Start")
        out.pop(0)
    return out


def osrm_route(mode, origin, destination):
    """Rad, zu Fuss oder Auto ueber OSRM (ohne Verkehr); beim Auto mit den Alternativen,
    die OSRM findet (unter "alternatives")."""
    url = "%s/routed-%s/route/v1/driving/%.6f,%.6f;%.6f,%.6f" % (
        OSRM_URL, OSRM_PROFILES[mode], origin["longitude"], origin["latitude"],
        destination["longitude"], destination["latitude"])
    params = {"overview": "full", "geometries": "polyline6", "steps": "true"}
    if mode == "car":
        params["alternatives"] = str(ALT_MAX)
    data = request_json(url, params=params)
    if not isinstance(data, dict) or data.get("code") != "Ok" or not data.get("routes"):
        if isinstance(data, dict) and data.get("code") in ("NoRoute", "NoSegment"):
            raise NoResult("No route found.")
        raise ServiceError("OSRM: %s" % (data.get("code") if isinstance(data, dict) else "?"))
    routes = []
    for route in data["routes"]:
        leg = (route.get("legs") or [{}])[0]
        routes.append({"mode": mode, "duration": float(route["duration"]), "distance": float(route["distance"]),
                       "summary": leg.get("summary") or "", "steps": condense_steps(leg.get("steps") or [], mode),
                       "coords": decode_polyline(route.get("geometry") or "", 6), "traffic": [], "delay": 0,
                       "source": "osrm", "live": False})
    return dict(routes[0], alternatives=routes[1:])


def tomtom_route(mode, origin, destination, key, when=None):
    """Rad, zu Fuss oder Auto ueber TomTom, mit aktuellem Verkehr (Stau, Sperren,
    Baustellen). when: (Zeit, Ankunft?) oder None fuer jetzt."""
    points = "%.6f,%.6f:%.6f,%.6f" % (origin["latitude"], origin["longitude"],
                                      destination["latitude"], destination["longitude"])
    params = [("key", key), ("travelMode", TOMTOM_MODES[mode]), ("routeType", "fastest"),
              ("instructionsType", "text"), ("language", "en-GB")]
    if mode == "car":                           # Stau zaehlt nur fuers Auto; Sperren beachtet TomTom immer
        params += [("traffic", "true"), ("sectionType", "traffic"), ("computeTravelTimeFor", "all"),
                   ("maxAlternatives", str(ALT_MAX)), ("alternativeType", "anyRoute")]
    if when:
        stamp = dt.datetime.fromtimestamp(when[0], VIENNA).strftime("%Y-%m-%dT%H:%M:%S")
        params.append(("arriveAt" if when[1] else "departAt", stamp))
    else:
        params.append(("departAt", "now"))
    try:
        data = request_json(TOMTOM_ROUTE % points, params=params)
    except ServiceError as exc:
        if isinstance(exc, KeyRejected) or "HTTP 400" not in str(exc):
            raise
        # Manche Optionen gibt es nicht fuer jedes Verkehrsmittel: dann schlicht
        data = request_json(TOMTOM_ROUTE % points, params=[p for p in params if p[0] in (
            "key", "travelMode", "traffic", "instructionsType", "language", "departAt", "arriveAt")])
    routes = data.get("routes") if isinstance(data, dict) else None
    if not routes:
        raise NoResult("No route found.")
    found = [tomtom_parse(route, mode) for route in routes if isinstance(route, dict)]
    return dict(found[0], alternatives=found[1:])


def tomtom_parse(route, mode):
    """Eine Route von TomTom in unserer Form: Strecke, Staus, Strassen der Reihe nach."""
    summary = route.get("summary") or {}
    coords = [(p["longitude"], p["latitude"]) for leg in route.get("legs") or [] for p in leg.get("points") or []
              if isinstance(p, dict) and "latitude" in p]
    traffic = []
    for sec in route.get("sections") or []:
        if sec.get("sectionType") != "TRAFFIC":
            continue
        a, b = sec.get("startPointIndex", 0), sec.get("endPointIndex", 0)
        traffic.append({"category": sec.get("simpleCategory") or "OTHER", "delay": sec.get("delayInSeconds") or 0,
                        "magnitude": sec.get("magnitudeOfDelay") or 0, "speed": sec.get("effectiveSpeedInKmh"),
                        "coords": coords[a:b + 1]})
    steps = []
    instructions = ((route.get("guidance") or {}).get("instructions")) or []
    for i, ins in enumerate(instructions):
        if ins.get("maneuver") == "ARRIVE":
            continue
        nxt = instructions[i + 1] if i + 1 < len(instructions) else None
        meters = (nxt.get("routeOffsetInMeters", 0) - ins.get("routeOffsetInMeters", 0)) if nxt else 0
        numbers = [n for n in ins.get("roadNumbers") or [] if n]
        name = ins.get("street") or ", ".join(numbers) or {"bike": "Cycle path", "walk": "Footpath", "car": "Road"}[mode]
        if steps and steps[-1]["name"] == name:
            steps[-1]["distance"] += meters
            continue
        steps.append({"name": name, "road": numbers[0] if numbers else name, "turn": ins.get("message") or "Continue",
                      "distance": meters})
    departure = iso_time(summary.get("departureTime"))
    return {"mode": mode, "duration": float(summary.get("travelTimeInSeconds") or 0),
            "distance": float(summary.get("lengthInMeters") or 0), "summary": "", "steps": steps[:60],
            "coords": coords, "traffic": traffic, "delay": float(summary.get("trafficDelayInSeconds") or 0),
            "no_traffic": summary.get("noTrafficTravelTimeInSeconds"), "start": departure,
            "source": "tomtom", "live": True}


def direct_route(mode, origin, destination, key=None, when=None):
    """Rad, zu Fuss oder Auto: mit TomTom-Schluessel mit aktuellem Verkehr, sonst (und
    wenn TomTom gerade nicht antwortet) ueber OSRM. Ein abgelehnter Schluessel wird
    gemeldet (warning)."""
    warning = None
    route = None
    if key:
        try:
            route = tomtom_route(mode, origin, destination, key, when)
        except KeyRejected as exc:
            warning = str(exc)
        except (ServiceError, Offline, ValueError, KeyError, TypeError) as exc:
            log("TomTom %s route failed (%s) - using OSRM" % (mode, exc))
            warning = "TomTom did not answer - shown without traffic."
    if route is None:
        route = osrm_route(mode, origin, destination)
    routes = [route] + (route.pop("alternatives", None) or [])
    routes = sensible_routes(routes) if mode == "car" else routes[:1]
    label_routes(routes)
    for each in routes:
        each["warning"] = warning if each["source"] == "osrm" else None
        each["tz"] = origin.get("tz")          # Uhrzeiten in der Zeit des Starts
    return dict(routes[0], alternatives=routes[1:])


def shared(route, other, step=0.0002):
    """Welcher Teil von route (0 bis 1, nach Laenge) ueber dieselben Strassen fuehrt wie
    other: Rasterzellen von rund 20 m entlang other, je Stueck von route die Mitte."""
    cells = set()
    coords = other.get("coords") or []
    for (x0, y0), (x1, y1) in zip(coords, coords[1:]):
        n = max(1, int(max(abs(x1 - x0), abs(y1 - y0)) / step))
        for i in range(n + 1):
            cells.add((round((x0 + (x1 - x0) * i / n) / step), round((y0 + (y1 - y0) * i / n) / step)))
    total = same = 0.0
    coords = route.get("coords") or []
    for (x0, y0), (x1, y1) in zip(coords, coords[1:]):
        meters = distance_m(y0, x0, y1, x1)
        cx, cy = round((x0 + x1) / 2 / step), round((y0 + y1) / 2 / step)
        total += meters
        if any((cx + dx, cy + dy) in cells for dx in (-1, 0, 1) for dy in (-1, 0, 1)):
            same += meters
    return same / total if total else 1.0


def sensible_routes(routes):
    """Die schnellste Autoroute und Alternativen zur Wahl: hoechstens ALT_SLOWER (bzw.
    ALT_SLOWER_SHARE) langsamer und zu weniger als ALT_SHARED auf denselben Strassen
    wie eine schnellere - zusammen hoechstens ALT_MAX, die schnellste zuerst."""
    routes = sorted((r for r in routes if r.get("coords")), key=lambda r: r["duration"]) or routes[:1]
    limit = routes[0]["duration"] + max(ALT_SLOWER, ALT_SLOWER_SHARE * routes[0]["duration"])
    keep = []
    for route in routes:
        if keep and route["duration"] > limit:
            break
        if any(shared(route, other) >= ALT_SHARED for other in keep):
            continue
        keep.append(route)
        if len(keep) == ALT_MAX:
            break
    return keep


GENERIC_ROADS = ("Road", "Cycle path", "Footpath")


def road_lengths(route):
    lengths = {}
    for step in route.get("steps") or []:
        road = step.get("road") or step.get("name")
        if road and road not in GENERIC_ROADS:
            lengths[road] = lengths.get(road, 0) + (step.get("distance") or 0)
    return lengths


def label_routes(routes):
    """"via" je Route: ihre laengste Strasse (die Nummer, wo es eine gibt) und dazu die
    laengste, die nur sie nimmt - so unterscheiden sich Alternativen auf einen Blick
    ("A1, Hauptstraße" und "A1, Bahnhofstraße"). Eine einzelne Route: die zwei laengsten."""
    roads = [sorted(road_lengths(r).items(), key=lambda kv: -kv[1]) for r in routes]
    for i, route in enumerate(routes):
        mine = roads[i]
        if not mine:
            route["via"] = route.get("summary") or ""
            continue
        others = {name for j, theirs in enumerate(roads) if j != i for name, meters in theirs if meters >= 300}
        parts = [mine[0][0]]
        own = next((name for name, meters in mine[1:] if name not in others and meters >= 200), None)
        if own is None and len(mine) > 1 and (len(routes) == 1 or mine[0][0] in others):
            own = mine[1][0]
        if own:
            parts.append(own)
        route["via"] = ", ".join(parts)


def check_tomtom_key(key):
    """Schluessel pruefen: eine kurze Autoroute in Wien. -> None oder Fehlertext."""
    try:
        route = tomtom_route("car", {"latitude": 48.2085, "longitude": 16.3721},
                             {"latitude": 48.2104, "longitude": 16.3640}, key)
    except KeyRejected:
        return "TomTom rejected this key."
    except Offline:
        return "No connection - try again when you are online."
    except (ServiceError, NoResult) as exc:
        return "TomTom answered: %s" % exc
    except Exception as exc:  # noqa: BLE001 - lieber eine Meldung als ein haengendes Fenster
        log("unexpected TomTom answer: %s: %s" % (type(exc).__name__, exc))
        return "TomTom answered unexpectedly - see the journal."
    if not route.get("coords"):
        return "TomTom answered without a route."
    return None


def map_url(mode, origin, destination):
    return MAP_URL % (OSRM_PROFILES[mode], origin["latitude"], origin["longitude"],
                      destination["latitude"], destination["longitude"])


# ------------------------------------------------------------------ Einstellungen und Cache

def clean_place(place):
    """Ort pruefen und vereinheitlichen; None ohne gueltige Koordinaten."""
    if not isinstance(place, dict):
        return None
    try:
        lat, lon = float(place["latitude"]), float(place["longitude"])
    except (KeyError, TypeError, ValueError):
        return None
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        return None
    kind = place.get("type") if place.get("type") in ("S", "A", "P", "C") else "C"
    out = {"name": str(place.get("name") or "%.4f, %.4f" % (lat, lon)), "sub": str(place.get("sub") or ""),
           "lid": str(place["lid"]) if place.get("lid") else None, "type": kind, "latitude": lat, "longitude": lon}
    for extra in ("tz", "motis"):               # Zeitzone und Haltestelle bei Transitous
        if place.get(extra):
            out[extra] = str(place[extra])
    return out


def clean_saved(place):
    """Gespeichertes Ziel: ein Ort, dazu der eigene Name ("label"), falls vergeben."""
    out = clean_place(place)
    text = str(place.get("label") or "").strip()[:LABEL_MAX] if out else ""
    if text and text != out["name"]:
        out["label"] = text
    return out


def same_place(a, b):
    """Derselbe Ort: gleicher Name (der eigene eines gespeicherten Ziels steht extra) an
    derselben Stelle."""
    return a["name"] == b["name"] and distance_m(a["latitude"], a["longitude"], b["latitude"], b["longitude"]) < 20


def place_title(place):
    """So heisst ein Ort im Feld und in den Listen: ein gespeichertes Ziel mit eigenem Namen so."""
    return place.get("label") or place["name"]


def place_sub(place):
    """Die zweite Zeile darunter - mit eigenem Namen auch, welcher Ort es ist."""
    if place.get("label"):
        return " · ".join(t for t in (place["name"], place.get("sub")) if t)
    return place.get("sub") or ""


def clean_stop(stop):
    if not isinstance(stop, dict) or not stop.get("name"):
        return None
    ids = {k: str(v) for k, v in (stop.get("ids") or {}).items() if k in SOURCE_NAMES and v}
    if not ids and stop.get("lid"):             # Stand von Version 1: nur die ÖBB-Kennung
        ids = {"oebb": str(stop["lid"])}
    if not ids:
        return None
    walk = stop.get("walk")
    serve = [s for s in stop.get("serve") or [] if s in ids or s == "oebb" and ids.get("oebb")]
    return {"key": str(stop.get("key") or ids.get("oebb") or next(iter(ids.values()))), "name": str(stop["name"]),
            "latitude": float(stop.get("latitude") or 0), "longitude": float(stop.get("longitude") or 0),
            "kinds": [k for k in stop.get("kinds") or [] if k in KIND_NAMES],
            "distance": stop.get("distance") if isinstance(stop.get("distance"), (int, float)) else None,
            "walk": float(walk) if isinstance(walk, (int, float)) else None, "ids": ids,
            "serve": serve or None, "learned": float(stop.get("learned") or 0)}


def load_settings():
    """{"home", "stops", "prefix", "saved", "recent", "tomtom_key", "traffic_layer",
    "filters"}; ohne Datei (erster Start) leer. filters bleiben auch fuer abgewaehlte
    Haltestellen stehen - hakt man sie wieder an, gilt ihr Filter wieder."""
    try:
        with open(SETTINGS_FILE, encoding="utf-8") as fh:
            data = json.load(fh)
    except FileNotFoundError:
        data = {}
    except (OSError, ValueError) as exc:
        log("could not read %s: %s" % (SETTINGS_FILE, exc))
        data = {}
    if not isinstance(data, dict):
        data = {}
    stops = [s for s in (clean_stop(s) for s in data.get("stops") or []) if s][:MAX_STOPS]
    key = str(data.get("tomtom_key") or "").strip()
    filters = data.get("filters") if isinstance(data.get("filters"), dict) else {}
    filters = {str(k): r for k, r in ((k, clean_rules(v)) for k, v in filters.items()) if r}
    return {"home": clean_place(data.get("home")), "stops": stops, "prefix": str(data.get("prefix") or ""),
            "saved": [p for p in (clean_saved(p) for p in data.get("saved") or []) if p][:SAVED_MAX],
            "recent": [p for p in (clean_place(p) for p in data.get("recent") or []) if p][:RECENT_MAX],
            "tomtom_key": key or None, "traffic_layer": bool(data.get("traffic_layer", True)), "filters": filters}


def write_json(path, value, indent=None, private=False):
    tmp = "%s.%d.tmp" % (path, os.getpid())
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(tmp, "w", encoding="utf-8") as fh:
            if private:                         # Schluessel und Adresse: nur fuer den Benutzer lesbar
                os.fchmod(fh.fileno(), 0o600)
            json.dump(value, fh, ensure_ascii=False, indent=indent)
            fh.write("\n")
        os.replace(tmp, path)
    except OSError as exc:
        log("could not write %s: %s" % (path, exc))


def save_settings(settings):
    write_json(SETTINGS_FILE, settings, indent=1, private=True)


def reorder_cache(cache, keys):
    """Der Stand in der neuen Reihenfolge der Haltestellen (keys) - Umsortieren laedt
    nichts neu. None, wenn er zu anderen Haltestellen gehoert."""
    if not cache or sorted(cache.get("stops") or []) != sorted(keys):
        return None
    boards = dict(zip(cache["stops"], cache["boards"]))
    return dict(cache, stops=list(keys), boards=[boards.get(k) for k in keys])


def load_cache(settings):
    """Letzter Stand, aber nur, wenn er zu den gewaehlten Haltestellen gehoert."""
    try:
        with open(CACHE_FILE, encoding="utf-8") as fh:
            cache = json.load(fh)
        if cache["stops"] == [stop_key(s) for s in settings.get("stops") or []] \
                and isinstance(cache["boards"], list) and isinstance(cache["fetched_at"], (int, float)):
            return cache
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return None


# Das Tray-Symbol: das oesterreichische Haltestellenschild (H im Kreis an der Stange),
# weiss im 24er-Raster mit der Strichstaerke der Pomodoro-Stoppuhr. Unter einem Namen
# auf -symbolic faerbt COSMIC es wie die Systemsymbole ein.
SVG_HEAD = '<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24">'
TRAY_SVG = (SVG_HEAD + '<g fill="none" stroke="#ffffff" stroke-width="2.1" stroke-linecap="round" '
            'stroke-linejoin="round"><circle cx="12" cy="9.2" r="6.6"/><path d="M12 15.8 V21.8"/>'
            '<path d="M9.6 6.2 V12.2 M14.4 6.2 V12.2 M9.6 9.2 H14.4"/></g></svg>\n')
# Das Logo fuer Starter und Fenster: das Schild in seinen echten Farben (gelb, gruenes
# H) auf einer Graphit-Kachel wie das Pomodoro-Logo.
TILE = "M8 1 H16 C20.4 1 23 3.6 23 8 V16 C23 20.4 20.4 23 16 23 H8 C3.6 23 1 20.4 1 16 V8 C1 3.6 3.6 1 8 1 Z"
LOGO_SVG = (SVG_HEAD + '<path d="%s" fill="#414853"/>' % TILE
            + '<path d="M12 15.4 V20.6" stroke="#c9ced6" stroke-width="1.8" stroke-linecap="round"/>'
              '<circle cx="12" cy="9.6" r="6" fill="#f6c915"/>'
              '<path d="M9.8 6.9 V12.3 M14.2 6.9 V12.3 M9.8 9.6 H14.2" fill="none" stroke="#1d7a45" '
              'stroke-width="2" stroke-linecap="round"/></svg>\n')
# Symbole fuer Menue und Fenster - das Cosmic-Theme hat keine fuer Verkehrsmittel.
# Linien im 16er-Raster wie bei Adwaita und den Wetter-Symbolen.
_SYMBOL = ('<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 16 16">'
           '<g fill="none" stroke="#ffffff" stroke-width="1.5" stroke-linecap="round" '
           'stroke-linejoin="round">%s</g>%s</svg>\n')


def _dots(*points, r=0.8):
    return "".join('<circle cx="%s" cy="%s" r="%s" fill="#ffffff"/>' % (x, y, r) for x, y in points)


_STAR = "M8 1.85 L9.62 6.23 L14.28 6.41 L10.62 9.3 L11.88 13.79 L8 11.2 L4.12 13.79 L5.38 9.3 L1.72 6.41 L6.38 6.23 Z"

SYMBOLS = {
    "stop": _SYMBOL % ('<circle cx="8" cy="6.25" r="4.75"/><path d="M8 11 V14.75"/>'
                       '<path d="M6.4 4.25 V8.25 M9.6 4.25 V8.25 M6.4 6.25 H9.6"/>', ""),
    "tram": _SYMBOL % ('<path d="M6 1.5 H10 M8 1.5 V3.5"/><rect x="3.75" y="3.5" width="8.5" height="8.5" rx="2"/>'
                       '<path d="M3.75 7.75 H12.25"/><path d="M5.75 14.5 L6.5 12 M10.25 14.5 L9.5 12"/>',
                       _dots((6, 9.9), (10, 9.9))),
    "bus": _SYMBOL % ('<rect x="3.5" y="2" width="9" height="10" rx="2"/><path d="M3.5 7.25 H12.5"/>'
                      '<path d="M5.5 12 V13.75 M10.5 12 V13.75"/><path d="M1.75 4.5 V6.5 M14.25 4.5 V6.5"/>',
                      _dots((5.9, 9.6), (10.1, 9.6))),
    "train": _SYMBOL % ('<path d="M3.75 12.25 V5.5 C3.75 3.3 5.6 2 8 2 C10.4 2 12.25 3.3 12.25 5.5 V12.25 Z"/>'
                        '<path d="M3.75 7.25 H12.25"/><path d="M5.75 14.5 L6.5 12.25 M10.25 14.5 L9.5 12.25"/>',
                        _dots((6, 10), (10, 10))),
    "subway": _SYMBOL % ('<rect x="2.75" y="2.75" width="10.5" height="10.5" rx="2.5"/>'
                         '<path d="M5.75 5.5 V8.6 A2.25 2.25 0 0 0 10.25 8.6 V5.5"/>', ""),
    "ferry": _SYMBOL % ('<path d="M1.75 9.5 H14.25 L12.5 13 H3.5 Z"/><path d="M4.75 9.5 V6.25 H11.25 V9.5"/>'
                        '<path d="M8 6.25 V3"/>', ""),
    "walk": _SYMBOL % ('<path d="M8.6 5 L7.6 9.4"/><path d="M7.6 9.4 L5.9 14.3 M7.6 9.4 L9.7 11.3 L10.1 14.3"/>'
                       '<path d="M5.2 7.9 L6.7 5.7 L8.6 5 L10.4 7 L12 7.6"/>', _dots((9.3, 2.4), r=1.45)),
    "bike": _SYMBOL % ('<circle cx="3.75" cy="10.75" r="2.75"/><circle cx="12.25" cy="10.75" r="2.75"/>'
                       '<path d="M3.75 10.75 L6.25 6.25 H10.75 L12.25 10.75 M6.25 6.25 L8.25 10.75 L10.75 6.25 '
                       'M3.75 10.75 H8.25"/><path d="M5.25 4.25 H7.25 M6.25 4.25 V6.25 M10.75 6.25 L10.25 4 H11.75"/>',
                       ""),
    "car": _SYMBOL % ('<path d="M2.25 11.25 V8.5 L3.75 4.6 C4 3.9 4.6 3.5 5.3 3.5 H10.7 C11.4 3.5 12 3.9 12.25 4.6 '
                      'L13.75 8.5 V11.25 Z"/><path d="M2.6 8 H13.4"/><path d="M4 11.25 V13 M12 11.25 V13"/>',
                      _dots((4.9, 9.65), (11.1, 9.65))),
    "home": _SYMBOL % ('<path d="M2.25 7.25 L8 2.5 L13.75 7.25"/><path d="M3.75 6 V13.5 H12.25 V6"/>'
                       '<path d="M6.75 13.5 V10 H9.25 V13.5"/>', ""),
    "route": _SYMBOL % ('<circle cx="4" cy="3.75" r="1.75"/><circle cx="12" cy="12.25" r="1.75"/>'
                        '<path d="M4 5.5 V7.5 C4 8.6 4.9 9.5 6 9.5 H10 C11.1 9.5 12 10 12 10.5"/>', ""),
    "pin": _SYMBOL % ('<path d="M8 14.5 C8 14.5 3.5 10.2 3.5 6.5 A4.5 4.5 0 0 1 12.5 6.5 C12.5 10.2 8 14.5 8 14.5 Z"/>'
                      '<circle cx="8" cy="6.5" r="1.6"/>', ""),
    "swap": _SYMBOL % ('<path d="M5 13.5 V2.5 M2.5 5 L5 2.5 L7.5 5"/><path d="M11 2.5 V13.5 M8.5 11 L11 13.5 L13.5 11"/>',
                       ""),
    "clock": _SYMBOL % ('<circle cx="8" cy="8" r="6"/><path d="M8 4.75 V8 L10.25 9.5"/>', ""),
    # Karte: Ampel fuer die Verkehrsebene, Rahmen fuer "ganze Strecke zeigen"
    "traffic": _SYMBOL % ('<rect x="5" y="1.75" width="6" height="12.5" rx="2"/>',
                          _dots((8, 4.6), (8, 8), (8, 11.4), r=1.05)),
    "fit": _SYMBOL % ('<path d="M2.5 6 V3.75 C2.5 3.06 3.06 2.5 3.75 2.5 H6 M10 2.5 H12.25 C12.94 2.5 13.5 3.06 13.5 3.75 '
                      'V6 M13.5 10 V12.25 C13.5 12.94 12.94 13.5 12.25 13.5 H10 M6 13.5 H3.75 C3.06 13.5 2.5 12.94 '
                      '2.5 12.25 V10"/><path d="M5.5 10.5 L10.5 5.5"/>', ""),
    "plus": _SYMBOL % ('<path d="M8 3 V13 M3 8 H13"/>', ""),
    # Haltestellen umsortieren
    "up": _SYMBOL % ('<path d="M3.5 10.25 L8 5.75 L12.5 10.25"/>', ""),
    "down": _SYMBOL % ('<path d="M3.5 5.75 L8 10.25 L12.5 5.75"/>', ""),
    "minus": _SYMBOL % ('<path d="M3 8 H13"/>', ""),
    # Filter einer Haltestelle: Trichter
    "filter": _SYMBOL % ('<path d="M2.5 3 H13.5 L9.25 8.25 V13 L6.75 11.75 V8.25 Z"/>', ""),
    "warning": _SYMBOL % ('<path d="M8 2.25 L14.25 13.25 H1.75 Z"/><path d="M8 6.5 V9.25"/>', _dots((8, 11.3), r=0.85)),
    # Umstieg: zwei Pfeile in entgegengesetzte Richtungen
    "change": _SYMBOL % ('<path d="M2.5 5.25 H12.5 M10 2.75 L12.5 5.25 L10 7.75"/>'
                         '<path d="M13.5 10.75 H3.5 M6 8.25 L3.5 10.75 L6 13.25"/>', ""),
    # Ziele: Stern zum Speichern (gefuellt = gespeichert), Kreuz zum Entfernen
    "star": _SYMBOL % ('<path d="%s"/>' % _STAR, ""),
    "starred": _SYMBOL % ('<path d="%s"/>' % _STAR, '<path d="%s" fill="#ffffff"/>' % _STAR),
    "close": _SYMBOL % ('<path d="M4.25 4.25 L11.75 11.75 M11.75 4.25 L4.25 11.75"/>', ""),
}
KIND_NAMES = {"train": "train", "subway": "U-Bahn", "tram": "tram", "bus": "bus", "ferry": "ferry"}
MODES = (("transit", ("tram",), "Transit"), ("mixed", ("bike", "tram"), "Bike + transit (park the bike at a stop)"),
         ("bike", ("bike",), "Bike"), ("walk", ("walk",), "Walk"), ("car", ("car",), "Car"))


# ------------------------------------------------------------------ Auswertung und Texte

def eff_time(item, key="planned"):
    """Tatsaechliche Zeit, wo es eine gibt, sonst die planmaessige. Fuer Abfahrten
    (planned/real) und Verbindungen bzw. Etappen (dep/dep_real, arr/arr_real)."""
    if key == "planned":
        return item["real"] if item.get("real") is not None else item["planned"]
    real = item.get(key + "_real")
    return real if real is not None else item[key]


def delay_minutes(planned, real):
    if planned is None or real is None:
        return 0
    return int(round((real - planned) / 60.0))


def signed(minutes):
    """+3, −1 (mit echtem Minuszeichen)."""
    return "+%d" % minutes if minutes > 0 else "−%d" % -minutes


def clock(ts, tz=None):
    """'18:42' in der Zeit des Orts (tz: Name der Zeitzone, ohne: Wien)."""
    t = dt.datetime.fromtimestamp(ts, zone(tz))
    return "%02d:%02d" % (t.hour, t.minute)


def when(ts, now):
    """'18:42' heute, 'Tue 18:42' innerhalb einer Woche, sonst '15 Sep 18:42' - in der
    Zeit dieses Rechners."""
    t = dt.datetime.fromtimestamp(ts)
    hm = "%02d:%02d" % (t.hour, t.minute)
    age = (dt.datetime.fromtimestamp(now).date() - t.date()).days
    if age == 0:
        return hm
    if 0 < age < 7:
        return "%s %s" % (DAYS[t.weekday()], hm)
    return "%d %s %s" % (t.day, MONTHS[t.month - 1], hm)


def duration_text(seconds):
    """'28 min', '1 h 05', '2 h'."""
    minutes = max(1, int(round(seconds / 60.0)))
    if minutes < 60:
        return "%d min" % minutes
    hours, rest = divmod(minutes, 60)
    return "%d h %02d" % (hours, rest) if rest else "%d h" % hours


def distance_text(meters):
    if meters is None:
        return ""
    if meters < 1000:
        return "%d m" % max(10, int(round(meters / 10.0)) * 10)
    return "%.1f km" % (meters / 1000.0)


def walk_minutes(seconds):
    return max(1, int(math.ceil((seconds or 0) / 60.0 - 1e-9)))


def stop_title(stop, prefix):
    """'Taubenmarkt · 3 min walk'."""
    name = short_name(stop["name"], prefix)
    return name if stop.get("walk") is None else "%s · %d min walk" % (name, walk_minutes(stop["walk"]))


def reachable(board, stop, now):
    """Abfahrten, die man zu Fuss von zuhause noch erreicht (Gehzeit auf ganze Minuten)."""
    limit = now + (walk_minutes(stop["walk"]) * 60 if stop.get("walk") is not None else 0) - REACH_SLACK
    return [d for d in board if eff_time(d) >= limit]


def dep_cells(dep, prefix=""):
    """Spalten einer Abfahrtszeile: Uhrzeit (tatsaechlich), Linie, Richtung, Verspaetung."""
    extra = "cancelled" if dep.get("cancelled") else ""
    if not extra:
        late = delay_minutes(dep["planned"], dep.get("real"))
        extra = signed(late) if late else ""
    return [clock(eff_time(dep), dep.get("tz")), dep["line"], short_name(dep["direction"], prefix), extra]


def updated_line(cache, state, now):
    """Steht im Menue hinter "Refresh now"."""
    if cache is None:
        if state in NOTES:
            return "No data yet · " + NOTES[state]
        return "Loading…" if state == "cached" else "No data yet"
    note = NOTES[state] if state in NOTES else ""
    missing = cache.get("missing") or []
    if not note and missing:
        note = "no %s data" % SOURCE_NAMES.get(missing[0], missing[0]) if len(missing) == 1 else "some data missing"
    return "Updated " + when(cache["fetched_at"], now) + (" · " + note if note else "")


def menu_rows(settings, cache, state, now):
    """Die Zeilen ueber dem Trenner, fuer Tray und --once: je Haltestelle eine
    Ueberschrift ("head"), darunter die noch erreichbaren Abfahrten ("dep") oder ein
    Hinweis ("note"). Ohne Zuhause eine Zeile, die zur Auswahl fuehrt ("action")."""
    if not settings.get("home"):
        return [{"kind": "action", "text": "Set your home to see departures…", "icon": "home"}]
    stops = settings.get("stops") or []
    if not stops:
        return [{"kind": "action", "text": "Choose stops near your home…", "icon": "stop"}]
    boards = (cache or {}).get("boards") or []
    quota = menu_quota(len(stops))
    rows, seen = [], set()
    for i, stop in enumerate(stops):
        rows.append({"kind": "head", "text": stop_title(stop, settings.get("prefix") or ""), "icon": "stop"})
        board = boards[i] if i < len(boards) else None
        if board is None:
            note = "Loading…" if state == "cached" else "No departures yet"
            rows.append({"kind": "note", "text": note, "icon": "clock"})
            continue
        rules = stop_rules(settings, stop)
        shown = 0
        for dep in reachable(board, stop, now):
            key = (dep.get("jid"), dep["planned"], dep.get("at")) if dep.get("jid") else (dep["line"], dep["planned"])
            if key in seen or dep_hidden(dep, rules):     # schon bei einer anderen Haltestelle, oder gefiltert
                continue
            seen.add(key)
            rows.append({"kind": "dep", "dep": dep, "stop": i, "icon": dep["kind"]})
            shown += 1
            if shown == quota:
                break
        if not shown:
            rows.append({"kind": "note", "icon": "clock", "text": no_departures(rules, state)})
    return rows


def no_departures(rules, state="ok", more=True):
    """Hinweis, wenn an einer Haltestelle nichts (mehr) faehrt - mit Filter: nichts davon."""
    if state != "ok":
        return "No departures known"
    return "No %s in the next %d min" % ("chosen lines" if rules else "more departures" if more else "departures",
                                         BOARD_MIN)


def terminal_lines(settings, cache, state, now):
    """Das Menue als Text fuer --once (Festbreitenschrift: Zeichen zaehlen genuegt)."""
    rows = menu_rows(settings, cache, state, now)
    cells = [dep_cells(r["dep"], settings.get("prefix") or "") for r in rows if r["kind"] == "dep"]
    widths = [max([len(c[i]) for c in cells] or [0]) for i in range(3)]
    lines, k = [], 0
    for row in rows:
        if row["kind"] == "dep":
            c = cells[k]
            k += 1
            text = "  %s  %s  %s" % (c[0].ljust(widths[0]), c[1].ljust(widths[1]), c[2].ljust(widths[2]))
            lines.append((text + ("  " + c[3] if c[3] else "")).rstrip())
        elif row["kind"] == "head":
            lines.append(row["text"])
        else:
            lines.append("  " + row["text"])
    lines.append(updated_line(cache, state, now))
    return lines


# ------------------------------------------------------------------ Symbole

def symbol_name(key):
    return "%s-%s-symbolic" % (APP_ICON, key)


def ensure_app_icons():
    """Logo und Menue-Symbole ins Icon-Theme legen (hicolor unter ~/.local/share/icons)."""
    wanted = [(APP_ICON, LOGO_SVG)] + [(symbol_name(k), svg) for k, svg in SYMBOLS.items()]
    for name, svg in wanted:
        path = os.path.join(APP_ICON_DIR, name + ".svg")
        try:
            with open(path, encoding="utf-8") as fh:
                if fh.read() == svg:
                    continue
        except OSError:
            pass
        try:
            os.makedirs(APP_ICON_DIR, exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(svg)
        except OSError as exc:
            log("could not write %s: %s" % (path, exc))


def tray_icon_file():
    """Das Tray-Symbol als Datei im Laufzeitordner (wie beim Wetter) - der Name traegt
    die PID, damit COSMIC nach einem Neustart nichts Altes aus dem Cache nimmt."""
    os.makedirs(ICON_DIR, exist_ok=True)
    name = "transit-tray-%d-symbolic" % os.getpid()
    for entry in os.listdir(ICON_DIR):
        if entry != name + ".svg":
            try:
                os.remove(os.path.join(ICON_DIR, entry))
            except OSError:
                pass
    with open(os.path.join(ICON_DIR, name + ".svg"), "w", encoding="utf-8") as fh:
        fh.write(TRAY_SVG)
    return name


# ------------------------------------------------------------------ Menueschrift

def menu_font():
    """Schrift des COSMIC-Menues: Einstellung interface_font, sonst die Vorgabe."""
    try:
        with open(MENU_FONT_FILE, encoding="utf-8") as fh:
            found = re.search(r'family:\s*"([^"]+)"', fh.read())
    except OSError:
        found = None
    return found.group(1) if found else "Open Sans"


class Spacer:
    """Misst Text in der Menueschrift und baut Leerraum genau bemessener Breite (wie
    beim Wetter). COSMIC setzt das Menue proportional - nur so stehen Spalten buendig."""

    SPACES = (" ", " ", " ", " ")    # Ziffern-, Normal-, Schmal-, Haarbreite

    def __init__(self, family):
        self.layout = Pango.Layout.new(PangoCairo.FontMap.get_default().create_context())
        desc = Pango.FontDescription(family)
        desc.set_absolute_size(1000 * Pango.SCALE)  # Breiten direkt in Tausendstel-Geviert
        self.layout.set_font_description(desc)
        self.spaces = sorted(((self.width(c), c) for c in self.SPACES), reverse=True)

    def width(self, text):
        """Breite in Geviert."""
        self.layout.set_text(text, -1)
        return self.layout.get_extents()[1].width / Pango.SCALE / 1000.0

    def fill(self, em):
        """Leerzeichen, zusammen moeglichst genau em Geviert breit."""
        out = []
        for width, char in self.spaces:
            count = int(max(0.0, em) / width + 1e-9)
            out.append(char * count)
            em -= count * width
        if em > self.spaces[-1][0] / 2:           # Rest ueber halber Haarbreite
            out.append(self.spaces[-1][1])
        return "".join(out)

    def clip(self, text, em):
        """Text, der hoechstens em Geviert breit ist - sonst gekuerzt mit '…'."""
        if self.width(text) <= em:
            return text
        low, high = 0, len(text)
        while low < high:                       # laengster Anfang, der mit '…' passt
            mid = (low + high + 1) // 2
            if self.width(text[:mid].rstrip() + "…") <= em:
                low = mid
            else:
                high = mid - 1
        return text[:low].rstrip() + "…" if low else "…"

    def fit(self, variants):
        """Die erste Variante, die in eine Menuezeile passt, sonst die gekuerzte letzte."""
        found = next((v for v in variants if self.width(v) <= LINE_EM), None)
        return found if found is not None else self.clip(variants[-1], LINE_EM)


# ------------------------------------------------------------------ Tray

class Tray:
    """Symbol + Menue in der COSMIC-Statusleiste (StatusNotifierItem)."""

    def __init__(self):
        self.first_start = not os.path.exists(SETTINGS_FILE)
        self.settings = load_settings()
        self.cache = load_cache(self.settings)
        self.state = "cached"           # bis die erste Abfrage zurueck ist
        self.busy = self.again = False
        self.timer = None
        self.nm = None
        self.window = self.home_window = None
        self.shown, self.images, self.enabled = {}, {}, {}  # zuletzt gesetzte Texte, Bilder, Klickbarkeit
        self.spacer = Spacer(menu_font())
        self.slot_rows = []                 # Zeile je Slot, fuer den Klick
        self.tiles = TileCache()            # Kartenkacheln fuer beide Karten des Fensters
        self.tiles.key = self.settings.get("tomtom_key")
        self.surveys = {}                   # stop_key -> (Zeit, Abfahrten): welche Linien dort fahren

        menu = Gtk.Menu()
        # Ueberschriften, Abfahrten und Hinweise teilen sich feste Plaetze ("Slots") -
        # Zeilen verschieben kann das Menue nicht, nur Texte, Bilder und Sichtbarkeit.
        self.slots = []
        for n in range(SLOTS):
            item = self.image_item("", symbol_name("stop"))
            self.images[item] = symbol_name("stop")
            item.connect("activate", lambda _i, n=n: self.on_slot(n))
            menu.append(item)
            self.slots.append(item)
        menu.append(Gtk.SeparatorMenuItem())
        self.action_item(menu, "Plan a route…", symbol_name("route"), lambda _i: self.open_window("route"))
        # "Refresh now" traegt zugleich den Stand der letzten Abfrage.
        self.refresh_item = self.action_item(menu, REFRESH, "view-refresh-symbolic", lambda _i: self.refresh())
        self.action_item(menu, "Home & stops…", symbol_name("home"), lambda _i: self.open_home())
        self.action_item(menu, "Quit", "application-exit-symbolic", lambda _i: Gtk.main_quit())
        menu.show_all()

        # Das Symbol muss als Datei existieren, bevor der Indicator entsteht.
        self.indicator = AppIndicator.Indicator.new_with_path(
            "transit-tray", tray_icon_file(), AppIndicator.IndicatorCategory.APPLICATION_STATUS, ICON_DIR)
        self.indicator.set_title("Transit")
        self.indicator.set_menu(menu)
        self.indicator.set_status(AppIndicator.IndicatorStatus.ACTIVE)

        self.render()
        self.watch_network()
        GLib.timeout_add_seconds(TICK, self.on_tick)
        # Frischer Stand, etwa nach einem Neustart durch tray-wait: erst zur naechsten
        # regulaeren Abfrage wieder fragen.
        age = time.time() - self.cache["fetched_at"] if self.cache else POLL
        if 0 <= age < self.poll_interval() - 30:
            self.state = "ok"
            self.schedule(int(self.poll_interval() - age))
        else:
            self.refresh()
        if not self.settings.get("home") and self.first_start:
            GLib.timeout_add_seconds(2, lambda: self.open_home() or GLib.SOURCE_REMOVE)

    @staticmethod
    def image_item(text, icon):
        """Menuezeile mit Bild davor. Das Bild gibt die AppIndicator-Bibliothek nur
        bei Gtk.ImageMenuItem an COSMIC weiter - deshalb dieses (veraltete) Widget."""
        item = Gtk.ImageMenuItem(label=text)
        item.set_image(Gtk.Image.new_from_icon_name(icon, Gtk.IconSize.MENU))
        item.set_always_show_image(True)
        return item

    def action_item(self, menu, text, icon, callback):
        item = self.image_item(text, icon)
        item.connect("activate", callback)
        menu.append(item)
        return item

    def set_row(self, item, text, icon=None, enabled=True):
        """Beschriftung, Bild und Klickbarkeit nur bei Aenderung setzen - jede Aenderung
        geht per D-Bus an COSMIC. text None blendet die Zeile aus."""
        if self.shown.get(item, ()) != text:
            self.shown[item] = text
            item.set_label(text or "")
            item.set_visible(bool(text))
        if icon and self.images.get(item) != icon:
            self.images[item] = icon
            item.get_image().set_from_icon_name(icon, Gtk.IconSize.MENU)
        if text and self.enabled.get(item) != enabled:
            self.enabled[item] = enabled
            item.set_sensitive(enabled)

    def render(self):
        now = time.time()
        rows = menu_rows(self.settings, self.cache, self.state, now)[:SLOTS]
        texts = self.row_texts(rows)
        self.slot_rows = rows
        for n, item in enumerate(self.slots):
            if n < len(rows):
                row = rows[n]
                self.set_row(item, texts[n], symbol_name(row["icon"]), row["kind"] in ("dep", "action"))
            else:
                self.set_row(item, None)
        if not self.busy:               # waehrend einer Abfrage steht dort "Refreshing..."
            self.refresh_item.set_label(self.refresh_label(now))
        self.refresh_item.set_visible(bool(self.settings.get("home") and self.settings.get("stops")))
        if self.window:
            self.window.departures_changed()

    def refresh_label(self, now):
        updated = updated_line(self.cache, self.state, now)
        return self.fit(["%s · %s" % (REFRESH, updated), "%s · %s" % (REFRESH, updated.replace("Updated ", ""))])

    def fit(self, variants):
        """Die erste Variante, die in eine Menuezeile passt - je mit breiten Trennern
        (SEP), nur wenn das nicht passt mit schmalen."""
        return self.spacer.fit([v for text in variants for v in (text.replace(" · ", SEP), text)])

    def row_texts(self, rows):
        """Texte aller Zeilen. Abfahrten stehen in Spalten - Uhrzeit, Linie, Richtung,
        Verspaetung -, buendig in der Menueschrift; zu lange Richtungen werden gekuerzt,
        sonst bricht COSMIC die Zeile um."""
        deps = [dep_cells(r["dep"], self.settings.get("prefix") or "") for r in rows if r["kind"] == "dep"]
        dep_texts = iter(self.columns(deps))
        return [next(dep_texts) if r["kind"] == "dep" else self.fit([r["text"]]) for r in rows]

    def columns(self, cells):
        if not cells:
            return []
        width, fill = self.spacer.width, self.spacer.fill
        w_time = max(width(c[0]) for c in cells)
        w_line = max(width(c[1]) for c in cells)
        w_extra = max([width(c[3]) for c in cells if c[3]] or [0])
        room = LINE_EM - w_time - GAP_TIME - w_line - GAP_LINE - (GAP_EXTRA + w_extra if w_extra else 0)
        directions = [self.spacer.clip(c[2], max(room, 3.0)) for c in cells]
        w_dir = max(width(d) for d in directions)
        texts = []
        for (when_, line, _direction, extra), direction in zip(cells, directions):
            text = (when_ + fill(w_time - width(when_) + GAP_TIME) + line + fill(w_line - width(line) + GAP_LINE)
                    + direction)
            if extra:
                text += fill(w_dir - width(direction) + GAP_EXTRA) + extra
            texts.append(text.rstrip())
        return texts

    def on_slot(self, n):
        row = self.slot_rows[n] if n < len(self.slot_rows) else None
        if row is None:
            return
        if row["kind"] == "dep":
            stops = self.settings.get("stops") or []
            self.open_window("departures", dep=row["dep"],
                             stop=stops[row["stop"]] if row.get("stop") is not None and row["stop"] < len(stops) else None)
        elif row["kind"] == "action":
            self.open_home()

    def on_tick(self):
        """Verpasste Abfahrten fallen weg - ohne Abfrage."""
        self.render()
        return GLib.SOURCE_CONTINUE

    # -- Abfragen: im Hintergrund-Thread, Ergebnis zurueck in den GTK-Thread

    def poll_interval(self):
        if self.window and self.window.showing_departures():
            return POLL_WINDOW
        if self.cache and self.state == "ok" and not self.upcoming():
            return POLL_QUIET
        return POLL_METERED if self.metered() else POLL

    def upcoming(self):
        """Faehrt noch etwas, das der Filter zeigt? Sonst fragt das Widget seltener."""
        now = time.time()
        stops = self.settings.get("stops") or []
        return any(eff_time(d) >= now and not dep_hidden(d, stop_rules(self.settings, stop))
                   for stop, board in zip(stops, (self.cache or {}).get("boards") or []) for d in board or [])

    def metered(self):
        """Getaktete Verbindung (NetworkManager: ja oder vermutlich ja) - etwa der Handy-Hotspot."""
        value = self.nm.get_cached_property("Metered") if self.nm else None
        return value is not None and value.unpack() in (1, 3)

    def schedule(self, seconds):
        if self.timer:
            GLib.source_remove(self.timer)
        self.timer = GLib.timeout_add_seconds(max(1, int(seconds)), self.on_timer)

    def on_timer(self):
        self.timer = None
        self.refresh()
        return GLib.SOURCE_REMOVE

    def refresh(self):
        if not (self.settings.get("home") and self.settings.get("stops")):
            self.render()
            return                      # ohne Haltestellen gibt es nichts abzufragen
        if self.busy:
            self.again = True           # z. B. Netzwechsel waehrend einer Abfrage
            return
        self.busy = True
        self.refresh_item.set_label("Refreshing…")
        self.refresh_item.set_sensitive(False)
        settings = json.loads(json.dumps(self.settings))
        previous = json.loads(json.dumps(self.cache)) if self.cache else None
        threading.Thread(target=self.worker, args=(settings, previous), daemon=True).start()

    def worker(self, settings, previous):
        now = time.time()
        learned = {}
        for stop in settings["stops"]:
            # Welche Betreiber hier fahren - einmal die Woche frisch von der ÖBB-Tafel
            if stop.get("serve") and now - (stop.get("learned") or 0) < LEARN_AGE:
                continue
            try:
                serve, sure = learn_serves(stop, now)
            except (Offline, ServiceError, NoResult, KeyError, TypeError) as exc:
                log("could not learn the operators at %s (%s)" % (stop["name"], exc))
                continue
            stop["serve"] = serve
            stop["learned"] = now if sure else now - LEARN_AGE + 3600     # nachts nichts: in einer Stunde nochmal
            learned[stop_key(stop)] = (serve, stop["learned"], dict(stop["ids"]))
        cache, state, detail = fetch_state(settings, now, previous)
        if detail:
            log(detail)
        GLib.idle_add(self.apply, settings, cache, state, learned)

    def apply(self, settings, cache, state, learned=None):
        self.busy = False
        self.refresh_item.set_sensitive(True)
        keys = [stop_key(s) for s in self.settings.get("stops") or []]
        asked = [stop_key(s) for s in settings["stops"]]
        if asked != keys:
            if sorted(asked) != sorted(keys):
                self.again = False      # Haltestellen gewechselt, waehrend die Abfrage lief
                self.refresh()
                return GLib.SOURCE_REMOVE
            cache = reorder_cache(cache, keys)      # nur umsortiert: die Tafeln passen trotzdem
        if learned:
            for stop in self.settings["stops"]:
                if stop_key(stop) in learned:
                    stop["serve"], stop["learned"], stop["ids"] = learned[stop_key(stop)]
            save_settings(self.settings)
            if self.home_window:
                self.home_window.stops_changed()
        self.state = state
        if cache is not None:
            self.cache = cache
            write_json(CACHE_FILE, cache)
        self.render()                   # setzt auch die Beschriftung mit dem neuen Stand
        if self.again:
            self.again = False
            self.schedule(2)
        else:
            self.schedule(self.poll_interval() if state == "ok" else RETRY)
        return GLib.SOURCE_REMOVE

    def watch_network(self):
        """Nach jedem Netzwechsel neu abfragen - etwa sobald das WLAN nach dem Anmelden steht."""
        try:
            self.nm = Gio.DBusProxy.new_for_bus_sync(
                Gio.BusType.SYSTEM, Gio.DBusProxyFlags.NONE, None,
                "org.freedesktop.NetworkManager", "/org/freedesktop/NetworkManager",
                "org.freedesktop.NetworkManager", None)
        except GLib.Error as exc:
            log("NetworkManager not reachable (%s) - periodic refresh only" % exc.message)
            return
        self.nm.connect("g-properties-changed", self.on_network_changed)

    def on_network_changed(self, _proxy, changed, _invalidated):
        if {"PrimaryConnection", "Connectivity", "State"} & set(changed.unpack()):
            if self.busy:
                self.again = True       # die laufende Abfrage ging womoeglich noch ins alte Netz
            else:
                self.schedule(5)        # Wartezeit, bis Routen und DNS stehen

    # -- Einstellungen und Fenster

    def settings_changed(self, settings):
        """Aus dem Fenster "Home & stops": speichern und fuer die neuen Haltestellen abfragen."""
        stops_before = [stop_key(s) for s in self.settings.get("stops") or []]
        self.settings = settings
        save_settings(settings)
        self.tiles.key = settings.get("tomtom_key")
        if self.window:
            self.window.update_traffic_buttons()
        if [stop_key(s) for s in settings.get("stops") or []] != stops_before:
            self.cache = load_cache(settings)
            self.state = "cached"
            self.refresh()
        self.render()
        if self.window:
            self.window.home_changed()

    def move_stop(self, index, step):
        """Eine Haltestelle eins nach oben (-1) oder unten (+1): in dieser Reihenfolge
        stehen sie im Menue und bei den Abfahrten. Die Tafeln ruecken mit, nichts wird
        neu geladen."""
        stops = list(self.settings.get("stops") or [])
        other = index + step
        if not (0 <= index < len(stops) and 0 <= other < len(stops)):
            return
        stops[index], stops[other] = stops[other], stops[index]
        self.settings["stops"] = stops
        save_settings(self.settings)
        if self.cache:
            self.cache = reorder_cache(self.cache, [stop_key(s) for s in stops])
            if self.cache:
                write_json(CACHE_FILE, self.cache)
            else:
                self.state = "cached"
                self.refresh()
        self.render()
        if self.home_window:
            self.home_window.stops_changed()

    def set_filter(self, key, rules):
        """Welche Linien und Richtungen die Haltestelle key zeigt. Menue und Abfahrten
        filtern sofort aus dem letzten Stand; die Abfrage danach holt groessere Tafeln,
        falls nun zu wenig Gezeigtes dabei ist."""
        filters = dict(self.settings.get("filters") or {})
        if rules:
            filters[key] = rules
        else:
            filters.pop(key, None)
        self.settings["filters"] = filters
        save_settings(self.settings)
        self.render()
        if self.home_window:
            self.home_window.stops_changed()
        if any(stop_key(s) == key for s in self.settings.get("stops") or []):
            if self.busy:
                self.again = True
            else:
                self.schedule(3)        # wer mehrere Haken setzt, loest eine Abfrage aus

    def survey(self, stop, done):
        """Welche Linien an der Haltestelle fahren (fuer den Filter): die Abfahrten der
        naechsten Stunden, SURVEY_AGE lang gemerkt. done(Abfahrten oder None, Hinweis)."""
        key = stop_key(stop)
        known = self.surveys.get(key)
        if known and time.time() - known[0] < SURVEY_AGE:
            done(known[1], known[2])
            return
        stop = json.loads(json.dumps(stop))

        def work():
            try:
                deps, missing = survey_lines(stop, time.time())
                note = "No answer from %s - its lines may be missing." % ", ".join(
                    SOURCE_NAMES.get(m, m) for m in missing) if missing else None
            except Offline:
                deps, note = None, "No connection - these are the lines known so far."
            except NoResult:
                deps, note = [], None
            except Exception as exc:  # noqa: BLE001
                log("line survey at %s failed: %s: %s" % (stop["name"], type(exc).__name__, exc))
                deps, note = None, "The lines did not load - these are the ones known so far."
            GLib.idle_add(finish, deps, note)

        def finish(deps, note):
            if deps is not None:
                self.surveys[key] = (time.time(), deps, note)
            done(deps, note)
            return GLib.SOURCE_REMOVE

        threading.Thread(target=work, daemon=True).start()

    # -- Gespeicherte und letzte Ziele. Ein Ort steht in hoechstens einer der beiden Listen;
    # das Fenster baut seine Listen danach selbst neu auf.

    def remember(self, place):
        """Ein gesuchtes Ziel vorn in die Liste der letzten Ziele - ein gespeichertes nicht,
        das steht schon unter "Saved"."""
        if self.saved_index(place) is not None:
            return
        recent = [p for p in self.settings.get("recent") or [] if not same_place(p, place)]
        self.settings["recent"] = ([clean_place(place)] + recent)[:RECENT_MAX]
        save_settings(self.settings)

    def saved_index(self, place):
        return next((i for i, p in enumerate(self.settings.get("saved") or []) if same_place(p, place)), None)

    def save_place(self, place):
        """Ein Ziel speichern: hinten an die gespeicherten, aus den letzten heraus."""
        saved = list(self.settings.get("saved") or [])
        if self.saved_index(place) is not None or len(saved) >= SAVED_MAX:
            return
        self.settings["saved"] = saved + [clean_saved(place)]
        self.forget_recent(place)               # speichert auch

    def unsave_place(self, place):
        self.settings["saved"] = [p for p in self.settings.get("saved") or [] if not same_place(p, place)]
        save_settings(self.settings)

    def rename_saved(self, place, text):
        """Eigener Name; leer oder gleich dem Ortsnamen heisst: der Ortsname gilt."""
        index = self.saved_index(place)
        if index is None:
            return
        saved = list(self.settings["saved"])
        saved[index] = clean_saved(dict(saved[index], label=text)) or saved[index]
        self.settings["saved"] = saved
        save_settings(self.settings)

    def move_saved(self, index, step):
        saved = list(self.settings.get("saved") or [])
        other = index + step
        if 0 <= index < len(saved) and 0 <= other < len(saved):
            saved[index], saved[other] = saved[other], saved[index]
            self.settings["saved"] = saved
            save_settings(self.settings)

    def forget_recent(self, place):
        self.settings["recent"] = [p for p in self.settings.get("recent") or [] if not same_place(p, place)]
        save_settings(self.settings)

    def clear_recent(self):
        """Die letzten Ziele leeren; zurueck kommt die alte Liste (fuer "Undo")."""
        old = list(self.settings.get("recent") or [])
        self.settings["recent"] = []
        save_settings(self.settings)
        return old

    def restore_recent(self, old):
        """Undo nach dem Leeren: was inzwischen dazukam, bleibt vorn."""
        recent = list(self.settings.get("recent") or [])
        recent += [p for p in old if not any(same_place(p, q) for q in recent) and self.saved_index(p) is None]
        self.settings["recent"] = recent[:RECENT_MAX]
        save_settings(self.settings)

    def open_window(self, page="route", dep=None, stop=None, token=None):
        """token: Aktivierungs-Token des Starters - damit holt COSMIC das Fenster nach vorn."""
        if not self.window:
            self.window = TransitWindow(self, page)
        else:
            self.window.show_page(page)
        if dep is not None:
            self.window.select_departure(dep, stop)
        if token:
            self.window.window.set_startup_id(token)
        self.window.window.present()
        if page == "departures" and self.cache and time.time() - self.cache["fetched_at"] > POLL_WINDOW:
            self.refresh()

    def window_closed(self):
        self.window = None

    def open_home(self, token=None):
        if not self.home_window:
            self.home_window = HomeWindow(self)
        if token:
            self.home_window.window.set_startup_id(token)
        self.home_window.window.present()

    def home_closed(self):
        self.home_window = None




# ------------------------------------------------------------------ Fenster: Bausteine

# Die Farben liefert COSMIC: Es schreibt sie als @window_fg_color, @card_bg_color,
# @accent_color usw. nach ~/.config/gtk-3.0/gtk.css.
UI_CSS = """
.tr-body { padding: 14px 16px 16px; }
.tr-card {
    background-color: @card_bg_color;
    border: 1px solid alpha(@window_fg_color, 0.08);
    border-radius: 14px;
}
.tr-places { padding: 4px 6px 4px 12px; }
.tr-entry, .tr-entry:focus {
    background-color: transparent;
    background-image: none;
    border-color: transparent;
    box-shadow: none;
    min-height: 32px;
}
.tr-entry:focus { background-color: alpha(@window_fg_color, 0.05); }
.tr-rule { background-color: alpha(@window_fg_color, 0.08); min-height: 1px; }
.tr-list { background-color: transparent; padding: 4px; }
.tr-list row { border-radius: 10px; padding: 8px 10px; }
.tr-list row:hover { background-color: alpha(@window_fg_color, 0.06); }
.tr-list row:selected, .tr-list row:selected:hover, .tr-list row:selected:focus {
    background-color: alpha(@accent_color, 0.16);
    color: @window_fg_color;
}
.tr-list row:selected label { color: @window_fg_color; }
.tr-list row:selected .tr-leave { color: @accent_color; }
.tr-list row:selected .tr-late { color: @warning_color; }
.tr-list row:selected .tr-cancel { color: @error_color; }
.tr-list row:selected .tr-chip label { color: @accent_fg_color; }
.tr-list row.tr-head, .tr-list row.tr-head:hover { background-color: transparent; padding: 10px 10px 2px; }
.tr-mode {
    border-radius: 12px;
    padding: 5px 2px 4px;
    min-height: 0;
    background-image: none;
    box-shadow: none;
    border: 1px solid transparent;
    background-color: alpha(@window_fg_color, 0.06);
}
.tr-mode:hover { background-color: alpha(@window_fg_color, 0.10); }
.tr-mode:checked { background-color: alpha(@accent_color, 0.18); border-color: alpha(@accent_color, 0.65); }
.tr-mode:checked label, .tr-mode:checked .tr-glyph { color: @accent_color; }
.tr-chip { background-color: @accent_color; border-radius: 6px; padding: 1px 6px; }
.tr-chip label { color: @accent_fg_color; font-weight: 700; font-size: 12px; }
.tr-chip .tr-glyph { color: @accent_fg_color; }
.tr-chip.tr-cancelled { background-color: alpha(@window_fg_color, 0.25); }
.tr-time { font-weight: 700; }
.tr-big { font-weight: 700; font-size: 15px; }
.tr-title { font-weight: 700; font-size: 17px; }
.tr-name { font-weight: 600; }
.tr-sub { font-size: 12px; }
.tr-section { font-weight: 700; }
.tr-late { color: @warning_color; }
.tr-cancel { color: @error_color; }
.tr-leave { color: @accent_color; font-weight: 600; }
.tr-detail { padding: 14px 14px 16px; }
.tr-popover { padding: 4px; }
.tr-float {
    background-color: alpha(@card_bg_color, 0.97);
    border: 1px solid alpha(@window_fg_color, 0.10);
    border-radius: 14px;
    box-shadow: 0 6px 18px rgba(0, 0, 0, 0.35);
}
.tr-mapbtn {
    min-width: 34px;
    min-height: 34px;
    padding: 0;
    border-radius: 10px;
    background-image: none;
    box-shadow: none;
    border: 1px solid alpha(@window_fg_color, 0.16);
    background-color: alpha(@window_bg_color, 0.92);
}
.tr-mapbtn:hover { background-color: @window_bg_color; }
.tr-mapbtn:checked { background-color: alpha(@accent_color, 0.28); border-color: alpha(@accent_color, 0.75); }
.tr-mapbtn:checked .tr-glyph { color: @accent_color; }
.tr-mapcard { border-radius: 14px; }
.tr-order {
    min-width: 26px;
    min-height: 26px;
    padding: 0;
    border-radius: 8px;
    border: none;
    background-image: none;
    background-color: transparent;
    box-shadow: none;
}
.tr-order:hover { background-color: alpha(@window_fg_color, 0.10); }
.tr-order .tr-glyph { color: alpha(@window_fg_color, 0.70); }
.tr-order:hover .tr-glyph { color: @window_fg_color; }
.tr-order:disabled .tr-glyph { color: alpha(@window_fg_color, 0.22); }
.tr-order.tr-active .tr-glyph, .tr-order.tr-active:hover .tr-glyph { color: @accent_color; }
.tr-link {
    padding: 1px 7px;
    min-height: 0;
    min-width: 0;
    border-radius: 7px;
    border: none;
    background-image: none;
    background-color: transparent;
    box-shadow: none;
}
.tr-link label { font-size: 12px; font-weight: 600; color: alpha(@window_fg_color, 0.70); }
.tr-link:hover { background-color: alpha(@window_fg_color, 0.10); }
.tr-link:hover label { color: @window_fg_color; }
.tr-link.tr-active label { color: @accent_color; }
.tr-rename, .tr-rename:focus {
    min-height: 28px;
    padding: 0 8px;
    border-radius: 8px;
    border: 1px solid transparent;
    background-image: none;
    box-shadow: none;
    background-color: alpha(@window_fg_color, 0.06);
}
.tr-rename:focus { border-color: alpha(@accent_color, 0.65); }
.tr-chipbtn {
    padding: 2px;
    min-width: 0;
    min-height: 0;
    border-radius: 8px;
    border: none;
    background-image: none;
    background-color: transparent;
    box-shadow: none;
}
.tr-chipbtn:hover { background-color: alpha(@window_fg_color, 0.10); }
.tr-filter { padding: 8px 6px 4px; }
.tr-badge {
    border-radius: 6px;
    padding: 0 6px;
    font-size: 11px;
    background-color: alpha(@window_fg_color, 0.08);
}
"""
_ui_ready = False
LEFT_W = 340            # linke Spalte: Suche und Liste
FLOAT_W = 300           # die schwebende Karte mit dem Verlauf ueber der Landkarte
RAIL_W = 22             # die Linie der Zeitleiste
NODE_Y = 10.5           # Mitte der ersten Textzeile, dort sitzt der Punkt
DOT_STEP = 7            # Fussweg in der Zeitleiste: ein Punkt alle 7 px


def prepare_ui():
    global _ui_ready
    if _ui_ready:
        return
    provider = Gtk.CssProvider()
    provider.load_from_data(UI_CSS.encode("utf-8"))
    Gtk.StyleContext.add_provider_for_screen(Gdk.Screen.get_default(), provider,
                                             Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
    _ui_ready = True


def styled(widget, *classes):
    for cls in classes:
        if cls:
            widget.get_style_context().add_class(cls)
    return widget


def label(text, *classes, xalign=0.0, ellipsize=False, wrap=False):
    widget = styled(Gtk.Label(label=text, xalign=xalign), *classes)
    if ellipsize:
        widget.set_ellipsize(Pango.EllipsizeMode.END)
    if wrap:
        widget.set_line_wrap(True)
        widget.set_line_wrap_mode(Pango.WrapMode.WORD_CHAR)
    return widget


_GLYPHS = {}


def glyph_pixbuf(key, pixels, color):
    """Ein eigenes Symbol in der Farbe color, pixels gross (gecacht)."""
    rgb = "#%02x%02x%02x" % tuple(int(round(c * 255)) for c in (color.red, color.green, color.blue))
    cache_key = (key, pixels, rgb)
    if cache_key not in _GLYPHS:
        try:
            loader = GdkPixbuf.PixbufLoader.new_with_type("svg")
            loader.set_size(pixels, pixels)
            loader.write(SYMBOLS[key].replace("#ffffff", rgb).encode("utf-8"))
            loader.close()
            _GLYPHS[cache_key] = loader.get_pixbuf()
        except GLib.Error as exc:
            log("could not draw the symbol %s: %s" % (key, exc.message))
            _GLYPHS[cache_key] = None
    return _GLYPHS[cache_key]


class Glyph:
    """Eigenes Symbol in einem Fenster, in der Textfarbe gezeichnet. Als -symbolic-Bild
    ginge das nicht: GTK3 faerbt Symbole ein, indem es alle Pfade fuellt - aus diesen
    Linien-Symbolen wuerden Kleckse (im Menue zeichnet COSMIC sie selbst, dort passt es).
    Die Farbe kommt wie bei Text aus dem CSS, also auch dim-label und Auswahl."""

    def __init__(self, key, size, *classes):
        self.key, self.size = key, size
        if can_draw():
            self.widget = styled(Gtk.DrawingArea(), "tr-glyph", *classes)
            self.widget.set_size_request(size, size)
            self.widget.connect("draw", self.on_draw)
            self.widget.connect("style-updated", lambda widget: widget.queue_draw())
        else:                           # ohne python3-gi-cairo: dann eben die Kleckse
            self.widget = styled(Gtk.Image.new_from_icon_name(symbol_name(key), Gtk.IconSize.MENU), *classes)
            self.widget.set_pixel_size(size)
        self.widget.set_valign(Gtk.Align.CENTER)

    def set(self, key):
        if key == self.key:
            return
        self.key = key
        if isinstance(self.widget, Gtk.Image):
            self.widget.set_from_icon_name(symbol_name(key), Gtk.IconSize.MENU)
        else:
            self.widget.queue_draw()

    def on_draw(self, area, cr):
        ctx = area.get_style_context()
        color = ctx.get_color(ctx.get_state())
        scale = area.get_scale_factor()
        pixbuf = glyph_pixbuf(self.key, self.size * scale, color)
        if pixbuf is None:
            return False
        cr.save()
        cr.translate((area.get_allocated_width() - self.size) / 2.0, (area.get_allocated_height() - self.size) / 2.0)
        cr.scale(1.0 / scale, 1.0 / scale)
        Gdk.cairo_set_source_pixbuf(cr, pixbuf, 0, 0)
        cr.paint_with_alpha(color.alpha)
        cr.restore()
        return False


def icon(key, size=16, *classes):
    """Eigenes Symbol (SYMBOLS) als Glyph, sonst ein Symbol aus dem Icon-Theme."""
    if key in SYMBOLS:
        return Glyph(key, size, *classes).widget
    image = Gtk.Image.new_from_icon_name(key, Gtk.IconSize.MENU)
    image.set_pixel_size(size)
    return styled(image, *classes)


def chip(kind, line, cancelled=False):
    """Linie als tuerkises Kaestchen mit Verkehrsmittel: [Tram 1]."""
    box = styled(Gtk.Box(spacing=4, valign=Gtk.Align.CENTER), "tr-chip", "tr-cancelled" if cancelled else None)
    box.pack_start(icon(kind, 13), False, False, 0)
    box.pack_start(label(line), False, False, 0)
    return box


def when_clicked(button, callback):
    """callback erst nach dem Klick: Meist baut er die Liste neu auf, samt dem Knopf. Den
    Fokus nimmt der Knopf nicht - er bleibt etwa im Eingabefeld darueber."""
    def run():
        callback()
        return GLib.SOURCE_REMOVE
    button.set_focus_on_click(False)
    button.connect("clicked", lambda _b: GLib.idle_add(run))
    return button


def tool_button(key, tip, callback):
    """Kleiner flacher Knopf mit eigenem Symbol neben einem Eintrag: Pfeile, Stern, Kreuz."""
    button = styled(Gtk.Button(), "tr-order")
    button.add(icon(key, 14))
    button.set_tooltip_text(tip)
    button.set_valign(Gtk.Align.CENTER)
    return when_clicked(button, callback)


def link_button(text, callback, active=False):
    """Flacher Textknopf rechts in einer Ueberschrift: "Edit", "Clear", "Undo"."""
    button = styled(Gtk.Button(label=text), "tr-link", "tr-active" if active else None)
    button.set_valign(Gtk.Align.CENTER)
    return when_clicked(button, callback)


def place_row(place, key):
    """Ein Ort in einer Liste: Symbol, Name, darunter Adresse oder Gegend."""
    row = Gtk.Box(spacing=10)
    row.pack_start(icon(key, 16, "dim-label"), False, False, 0)
    text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=1)
    text.pack_start(label(place_title(place), "tr-name", ellipsize=True), False, False, 0)
    if place_sub(place):
        text.pack_start(label(place_sub(place), "tr-sub", "dim-label", ellipsize=True), False, False, 0)
    row.pack_start(text, True, True, 0)
    return row


def header_bar(win, subtitle=None):
    """Titelleiste mit Logo wie bei Wetter und Pomodoro."""
    win.set_icon_name(APP_ICON)
    bar = Gtk.HeaderBar(title="Transit", subtitle=subtitle, show_close_button=True)
    logo = Gtk.Image.new_from_icon_name(APP_ICON, Gtk.IconSize.LARGE_TOOLBAR)
    logo.set_pixel_size(22)
    bar.pack_start(logo)
    win.set_titlebar(bar)
    return bar


def theme_color(ctx, name, fallback):
    found, rgba = ctx.lookup_color(name)
    return rgba if found else Gdk.RGBA(*fallback, 1.0)


_drawing = None


def can_draw():
    """GTK uebergibt beim Zeichnen einen cairo-Kontext - dafuer braucht PyGObject das
    Paket python3-gi-cairo (steht in der Paketliste)."""
    global _drawing
    if _drawing is None:
        import gi
        try:
            gi.require_foreign("cairo")
            _drawing = True
        except ImportError:
            log("python3-gi-cairo is missing - symbols and the route line look plain")
            _drawing = False
    return _drawing


def draw_rail(area, cr, kind, before, after, end, minor):
    """Ein Stueck der Zeitleiste: Fahrt tuerkis, Fussweg gepunktet, Rad und Auto grau;
    bei einer Haltestelle ("node") der Punkt mit Linie davor und danach."""
    import cairo
    width, height = area.get_allocated_width(), area.get_allocated_height()
    ctx = area.get_style_context()
    fg = ctx.get_color(Gtk.StateFlags.NORMAL)
    accent = theme_color(ctx, "accent_color", (0.39, 0.82, 0.87))
    card = theme_color(ctx, "card_bg_color", (0.18, 0.18, 0.18))
    x = width // 2 + 0.5
    top = area.get_allocation().y       # die Punkte im Raster der ganzen Zeitleiste

    def segment(y0, y1, style):
        if not style or y1 <= y0:
            return
        cr.save()
        if style == "ride":
            cr.set_source_rgba(accent.red, accent.green, accent.blue, 1.0)
            cr.set_line_width(4)
        elif style == "walk":
            cr.set_source_rgba(fg.red, fg.green, fg.blue, 0.45)
            cr.set_line_width(3)
            cr.set_line_cap(cairo.LINE_CAP_ROUND)
            cr.set_dash([0.01, DOT_STEP - 0.01], (top + y0) % DOT_STEP)     # gleich weit, auch ueber Zeilen
        else:                                   # Rad, Auto
            cr.set_source_rgba(fg.red, fg.green, fg.blue, 0.5)
            cr.set_line_width(4)
        cr.move_to(x, y0)
        cr.line_to(x, y1)
        cr.stroke()
        cr.restore()

    if kind != "node":
        segment(0, height, kind)
        return False
    segment(0, NODE_Y, before)
    segment(NODE_Y, height, after)
    radius = 4.0 if minor else 6.0
    cr.arc(x, NODE_Y, radius, 0, 2 * math.pi)
    cr.set_source_rgba(card.red, card.green, card.blue, 1.0)
    cr.fill_preserve()
    color = accent if end else fg
    cr.set_source_rgba(color.red, color.green, color.blue, 1.0)
    cr.set_line_width(2.0 if minor else 2.5)
    cr.stroke()
    return False


class Timeline:
    """Ein Weg als Zeitleiste: links die Uhrzeit, in der Mitte die Linie, rechts
    Haltestelle bzw. Etappe."""

    def __init__(self):
        self.grid = Gtk.Grid(column_spacing=10, row_spacing=0)
        self.row = 0
        self.drawing = can_draw()

    def rail(self, kind, before=None, after=None, end=False, minor=False):
        area = Gtk.DrawingArea()
        area.set_size_request(RAIL_W, -1)
        if self.drawing:
            area.connect("draw", draw_rail, kind, before, after, end, minor)
        return area

    def attach(self, left, middle, right):
        self.grid.attach(left, 0, self.row, 1, 1)
        self.grid.attach(middle, 1, self.row, 1, 1)
        self.grid.attach(right, 2, self.row, 1, 1)
        self.row += 1

    def node(self, name, planned=None, real=None, sub=None, before=None, after=None, end=False, minor=False,
             cancelled=False, arrival=None, change=None, tz=None):
        """arrival: (planmaessig, tatsaechlich) der Ankunft, klein ueber der Abfahrt - bei
        einem Umstieg am selben Steig. change: Inhalt, der unter dem Namen steht. tz:
        Zeitzone des Orts (ohne: Wien)."""
        times = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, valign=Gtk.Align.START)
        times.set_size_request(42, -1)
        if arrival is not None and arrival[0] is not None:
            came = arrival[1] if arrival[1] is not None else arrival[0]
            times.pack_start(label(clock(came, tz), "tr-sub", "dim-label", xalign=1.0), False, False, 0)
        if planned is not None:
            moment = real if real is not None else planned
            times.pack_start(label(clock(moment, tz), "tr-time" if not minor else None, "dim-label" if minor else None,
                                   xalign=1.0), False, False, 0)
            late = delay_minutes(planned, real)
            if late:
                times.pack_start(label(signed(late), "tr-late", "tr-sub", xalign=1.0), False, False, 0)
        text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=1)
        text.pack_start(label(name, None if minor else "tr-name", wrap=True), False, False, 0)
        if cancelled:
            text.pack_start(label("cancelled", "tr-cancel", "tr-sub"), False, False, 0)
        if change is not None:
            text.pack_start(change, False, False, 2)
        if sub:
            text.pack_start(label(sub, "tr-sub", "dim-label", wrap=True), False, False, 0)
        text.set_margin_bottom(4 if minor else 10)
        self.attach(times, self.rail("node", before, after, end, minor), text)

    def leg(self, style, content):
        content.set_margin_top(2)
        content.set_margin_bottom(12)
        self.attach(Gtk.Box(), self.rail(style), content)


def ride_content(leg, prefix):
    """Inhalt einer Fahrt: Linie und Richtung, Dauer und Halte, aufklappbar die Halte."""
    box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
    head = Gtk.Box(spacing=8)
    head.pack_start(chip(leg["kind"], leg["line"], leg.get("cancelled")), False, False, 0)
    head.pack_start(label("→ " + short_name(leg["direction"], prefix), "tr-name", ellipsize=True), True, True, 0)
    box.pack_start(head, False, False, 0)
    parts = [duration_text(eff_time(leg, "arr") - eff_time(leg, "dep"))]
    stops = leg.get("stops") or []
    if stops:
        parts.append("%d stop%s" % (len(stops) + 1, "s" if stops else ""))
    if leg.get("cancelled"):
        box.pack_start(label("cancelled", "tr-cancel", "tr-sub"), False, False, 0)
    elif not leg.get("reachable", True):
        box.pack_start(label("this change may not work out", "tr-late", "tr-sub"), False, False, 0)
    who = leg.get("operator") or ""
    if leg.get("rt_source"):
        parts.append("live from " + leg["rt_source"])
    elif leg.get("dep") and leg["dep"] - time.time() < 7200:
        parts.append("timetable")
    if who:
        parts.insert(0, re.sub(r"\s+(GmbH.*|AG|Gesellschaft.*|& Co.*|-Standort.*)$", "", who))
    box.pack_start(label(" · ".join(parts), "tr-sub", "dim-label", wrap=True), False, False, 0)
    if stops:
        expander = Gtk.Expander(label="Stops in between")
        styled(expander.get_label_widget(), "tr-sub")
        grid = Gtk.Grid(column_spacing=10, row_spacing=2)
        grid.set_margin_top(4)
        for i, stop in enumerate(stops):
            if stop.get("time") is not None:
                grid.attach(label(clock(stop["real"] if stop.get("real") is not None else stop["time"],
                                        stop.get("tz") or leg.get("dep_tz")),
                                  "tr-sub", "dim-label", xalign=1.0), 0, i, 1, 1)
            grid.attach(label(short_name(stop["name"], prefix) + (" (cancelled)" if stop.get("cancelled") else ""),
                              "tr-sub", "dim-label", ellipsize=True), 1, i, 1, 1)
        expander.add(grid)
        box.pack_start(expander, False, False, 0)
    return box


def source_markup(prefix, source):
    """'Route by ÖBB' - bei Transitous mit Link auf deren Quellen (so verlangen sie es)."""
    name = SOURCE_NAMES.get(source or "", "")
    if not name:
        return None
    if source == "motis":
        return '%s <a href="%s">%s</a>' % (GLib.markup_escape_text(prefix), TRANSITOUS_SOURCES, name)
    return GLib.markup_escape_text("%s %s" % (prefix, name))


TIGHT_CHANGE = 2 * 60   # s: knapper Umstieg - orange
SAME_SPOT_M = 25        # so nah beieinander gilt ein Umstieg als "same stop"


def change_place(before, after):
    """Wo umgestiegen wird, wenn der Planer keinen Fussweg nennt: anderer Bahnsteig, eine
    andere Stelle der Haltestelle (mit Entfernung) - "same stop" nur, wenn beide Fahrten
    wirklich dort halten."""
    came, going = before.get("arr_platform"), after.get("dep_platform")
    if came and going and came != going:
        return " · platform %s → %s" % (came, going)
    a, b = before.get("to_coord"), after.get("from_coord")
    apart = distance_m(a[1], a[0], b[1], b[0]) if a and b else 0
    if apart > SAME_SPOT_M:
        return " · %s away" % distance_text(apart)
    if plain_name(before.get("to")) == plain_name(after.get("from")):
        return " · same stop"
    return ""


def change_content(walk, before, after):
    """Ein Umstieg zwischen zwei Fahrten: der Fussweg zur anderen Stelle (falls einer
    noetig ist, mit Treppe, Rolltreppe oder Lift) und die Zeit bis zur Abfahrt. Zu knapp
    (oder wegen Verspaetung nicht mehr zu schaffen) steht orange."""
    box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
    head = Gtk.Box(spacing=6)
    head.pack_start(icon("change", 14, "tr-leave"), False, False, 0)
    arrive, leave = eff_time(before, "arr"), eff_time(after, "dep")
    walking = (walk or {}).get("duration") or 0
    meters = (walk or {}).get("distance")
    text = "Change"
    if walk is not None and (meters or walking >= 60):
        text += " · walk %s" % duration_text(walking) + (" (%s)" % distance_text(meters) if meters else "")
    elif walk is None:
        text += change_place(before, after)
    head.pack_start(label(text, "tr-leave"), False, False, 0)
    box.pack_start(head, False, False, 0)
    spare = leave - arrive - (walking if meters or walking >= 60 else 0)
    total = leave - arrive
    if total < 0 or spare < 0:
        note, classes = "%s too late - may not work out" % duration_text(-min(total, spare)), ("tr-late", "tr-sub")
    elif spare < 60:
        note, classes = "no time to wait - tight change", ("tr-late", "tr-sub")
    else:
        note = "%s wait" % duration_text(spare) if walking >= 60 else "%s to change" % duration_text(total)
        classes = ("tr-late", "tr-sub") if total < TIGHT_CHANGE else ("tr-sub", "dim-label")
    if walk is not None and walk.get("levels"):          # "stairs up · 2 min wait"
        note = "%s · %s" % (walk["levels"], note)
    box.pack_start(label(note, *classes), False, False, 0)
    return box


def walk_content(leg):
    box = Gtk.Box(spacing=6)
    box.pack_start(icon("walk", 14, "dim-label"), False, False, 0)
    minutes, meters = (leg.get("duration") or 0) / 60.0, leg.get("distance")
    if minutes < 1 and not meters:
        text = "Change"
    else:
        text = "Walk %s" % duration_text(leg.get("duration") or 60)
        if meters:
            text += " · " + distance_text(meters)
    box.pack_start(label(text, "dim-label"), False, False, 0)
    return box


# Linie der Zeitleiste je Etappe: Fahrt tuerkis, Fussweg gepunktet, Rad grau
RAIL_STYLES = {"ride": "ride", "walk": "walk", "bike": "solo"}


def bike_content(leg, park=False):
    """Mit dem Rad: Dauer und Strecke; vor einer Fahrt der Hinweis, das Rad dort zu parken."""
    box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=1)
    head = Gtk.Box(spacing=6)
    head.pack_start(icon("bike", 14, "dim-label"), False, False, 0)
    text = "Cycle %s" % duration_text(leg.get("duration") or 60)
    if leg.get("distance"):
        text += " · " + distance_text(leg["distance"])
    head.pack_start(label(text, "dim-label"), False, False, 0)
    box.pack_start(head, False, False, 0)
    if park:
        box.pack_start(label("then park your bike at the stop", "tr-sub", "dim-label"), False, False, 0)
    return box


# ------------------------------------------------------------------ Ortssuche im Fenster

class PlaceEntry:
    """Eingabefeld fuer Start oder Ziel: Tippen sucht Haltestellen, Adressen und Ziele,
    die Treffer erscheinen darunter (Klick oder Enter fuer den ersten). Leer und mit
    Fokus zeigt es Zuhause, die gespeicherten und die letzten Ziele - letzte mit einem
    Kreuz zum Entfernen."""

    def __init__(self, owner, placeholder):
        self.owner = owner
        self.place = None
        self.quiet = False              # True, waehrend der Text von hier gesetzt wird
        self.serial = 0
        self.timer = None
        self.places = []
        self.entry = styled(Gtk.Entry(placeholder_text=placeholder, hexpand=True), "tr-entry")
        self.entry.connect("changed", self.on_changed)
        self.entry.connect("activate", self.on_activate)
        self.entry.connect("key-press-event", self.on_key)
        self.entry.connect("focus-in-event", self.on_focus_in)
        self.entry.connect("focus-out-event", self.on_focus_out)

        self.popover = styled(Gtk.Popover(relative_to=self.entry), "tr-popover")
        self.popover.set_modal(False)
        self.popover.set_position(Gtk.PositionType.BOTTOM)
        scroller = Gtk.ScrolledWindow(hscrollbar_policy=Gtk.PolicyType.NEVER,
                                      vscrollbar_policy=Gtk.PolicyType.AUTOMATIC)
        scroller.set_propagate_natural_height(True)
        scroller.set_max_content_height(360)
        scroller.set_size_request(300, -1)
        self.list = styled(Gtk.ListBox(selection_mode=Gtk.SelectionMode.NONE), "tr-list")
        self.list.connect("row-activated", self.on_row)
        self.list.connect("key-press-event", self.on_list_key)
        scroller.add(self.list)
        self.popover.add(scroller)
        scroller.show_all()

    def set_place(self, place, text=None):
        self.popover.popdown()
        self.quiet = True
        self.entry.set_text(text if text is not None else (place_title(place) if place else ""))
        self.quiet = False
        self.place = place
        self.entry.set_position(-1)

    def suggestions(self):
        """Ohne Suchtext: Zuhause, die gespeicherten und die letzten Ziele."""
        found = []
        settings = self.owner.tray.settings
        home = settings.get("home")
        if home:
            found.append(dict(home, name="Home", sub=home["name"], home=True))
        found.extend(dict(p, saved=True) for p in settings.get("saved") or [])
        found.extend(dict(p, recent=True) for p in settings.get("recent") or [])
        return found

    def on_changed(self, _entry):
        if self.quiet:
            return
        self.place = None
        self.owner.place_cleared(self)
        if self.timer:
            GLib.source_remove(self.timer)
        self.timer = GLib.timeout_add(300, self.on_timer)

    def on_timer(self):
        self.timer = None
        text = self.entry.get_text().strip()
        self.serial += 1
        if len(text) < 2:
            self.show_places(self.suggestions())
            return GLib.SOURCE_REMOVE
        self.show_places([], "Searching…")     # am Hotspot dauert es manchmal Sekunden
        threading.Thread(target=self.search, args=(text, self.serial), daemon=True).start()
        return GLib.SOURCE_REMOVE

    def search(self, text, serial):
        try:
            places, note = search_places(text, self.owner.tray.settings.get("home")), None
        except Offline:
            places, note = [], "No connection - try again when you are online."
        except Exception as exc:  # noqa: BLE001
            log("place search failed: %s: %s" % (type(exc).__name__, exc))
            places, note = [], "The search did not work - try again later."
        GLib.idle_add(self.found, serial, places, note)

    def found(self, serial, places, note):
        if serial != self.serial or self.owner.window is None:
            return GLib.SOURCE_REMOVE   # schon weiter getippt oder Fenster zu
        self.show_places(places, note or (None if places else "Nothing found."))
        return GLib.SOURCE_REMOVE

    def show_places(self, places, note=None):
        for child in self.list.get_children():
            child.destroy()
        self.places = places
        for place in places:
            key = "home" if place.get("home") else "starred" if place.get("saved") else \
                "clock" if place.get("recent") else "stop" if place["type"] == "S" else "pin"
            row = place_row(place, key)
            if place.get("recent"):
                row.pack_end(tool_button("close", "Remove from recent destinations", lambda p=place: self.forget(p)),
                             False, False, 0)
            self.list.add(row)
        if note:
            row = Gtk.ListBoxRow(activatable=False, selectable=False)
            row.add(label(note, "dim-label", wrap=True))
            self.list.add(row)
        self.list.show_all()
        if (places or note) and self.entry.has_focus():
            self.popover.popup()
        else:
            self.popover.popdown()

    def choose(self, place):
        self.popover.popdown()
        is_home = bool(place.get("home"))
        place = {k: v for k, v in place.items() if k not in ("home", "saved", "recent")}
        self.set_place(place)
        self.owner.place_chosen(self, place, is_home)

    def forget(self, place):
        """Kreuz neben einem letzten Ziel: weg damit, die Liste bleibt offen."""
        self.owner.tray.forget_recent(place)
        self.show_places(self.suggestions())
        self.owner.saved_changed()

    def on_row(self, _list, row):
        index = row.get_index()
        if index < len(self.places):
            self.choose(self.places[index])

    def on_activate(self, _entry):
        if self.timer:                  # Enter vor dem Ende der Tipp-Pause: jetzt suchen
            GLib.source_remove(self.timer)
            self.timer = None
        if self.places and self.popover.get_visible():
            self.choose(self.places[0])

    def on_key(self, _entry, event):
        if event.keyval in (Gdk.KEY_Down, Gdk.KEY_KP_Down) and self.popover.get_visible():
            row = self.list.get_row_at_index(0)
            if row is not None:
                row.grab_focus()
                return True
        if event.keyval == Gdk.KEY_Escape and self.popover.get_visible():
            self.popover.popdown()
            return True
        return False

    def on_list_key(self, _list, event):
        if event.keyval == Gdk.KEY_Escape:
            self.popover.popdown()
            self.entry.grab_focus()
            return True
        return False

    def on_focus_in(self, _entry, _event):
        if not self.entry.get_text().strip() or self.place is None and len(self.entry.get_text().strip()) < 2:
            self.show_places(self.suggestions())
        return False

    def on_focus_out(self, _entry, _event):
        GLib.timeout_add(200, self.hide_if_away)
        return False

    def hide_if_away(self):
        window = self.owner.window
        focus = window.get_focus() if window else None
        if focus is None or not (focus is self.entry or focus.is_ancestor(self.popover)):
            self.popover.popdown()
            if self.place is None and self.owner.window is not None:
                self.owner.place_left(self)
        return GLib.SOURCE_REMOVE




# ------------------------------------------------------------------ Karte

TILE_PX = 256                   # Kachelraster in logischen Pixeln (HiDPI-Kacheln haben 512 px)
MAP_MIN_Z, MAP_MAX_Z = 6, 19
FIT_MAX_Z = 16.5                # so nah zoomt "ganze Strecke" hoechstens
FLOW_MAX_AGE = 5 * 60           # Verkehrslage-Kacheln veralten schnell
TILE_RETRY = 60                 # fehlgeschlagene Kachel so lange nicht neu laden
MAP_BG = (0.93, 0.92, 0.89)     # bis die Kachel da ist
ROUTE_EDGE = (0.03, 0.17, 0.20)
ALT_RGB = (0.58, 0.62, 0.66)    # die anderen Autorouten
WALK_STEP = 13                  # Fussweg-Punkte: Abstand von Mitte zu Mitte (8 px gross, 5 px Luecke)
# Verkehr auf der Strecke nach TomTom (magnitudeOfDelay 1-4), Sperre dunkelrot
TRAFFIC_RGB = {0: (0.96, 0.62, 0.04), 1: (0.96, 0.62, 0.04), 2: (0.93, 0.40, 0.07), 3: (0.84, 0.13, 0.13),
               4: (0.55, 0.05, 0.05)}
SIGN_YELLOW, SIGN_GREEN = (0.965, 0.788, 0.082), (0.114, 0.478, 0.271)


COVER_MARGIN = 0.025            # Grad, rund 2 km: so weit weg von der Grenze gilt eine Kachel als "in"
BORDER_ERROR = 0.015            # Grad: so ungenau ist die Grenze oben
# An der Grenze laeuft basemap.at weich in OpenStreetMap aus (edge_tile, braucht numpy):
EDGE_BAND = 14                  # px: so weit innen an der Grenze verschwindet der lila Saum von basemap.at
EDGE_FADE = 6                   # px: so weich blenden die Flaechen von basemap.at an der Grenze aus
EDGE_MEMORY = 64                # so viele ausgeblendete Randkacheln im Speicher
_COVER = {}
np = None                       # numpy, erst fuer die erste Randkachel geladen (edge_numpy)
AUSTRIA_EDGES = [(a[0], a[1], b[0], b[1]) for ring in AUSTRIA_RINGS for a, b in zip(ring, ring[1:] + ring[:1])]


def tile_box(z, x, y):
    """Eine Kachel als lon/lat-Rechteck (west, sued, ost, nord)."""
    n = 2.0 ** z

    def lat(row):
        return math.degrees(math.atan(math.sinh(math.pi * (1 - 2 * row / n))))
    return x / n * 360.0 - 180.0, lat(y + 1), (x + 1) / n * 360.0 - 180.0, lat(y)


def segment_in_box(x0, y0, x1, y1, box):
    """Beruehrt die Strecke das Rechteck (west, sued, ost, nord)? Liang-Barsky."""
    if max(x0, x1) < box[0] or min(x0, x1) > box[2] or max(y0, y1) < box[1] or min(y0, y1) > box[3]:
        return False
    t0, t1 = 0.0, 1.0
    dx, dy = x1 - x0, y1 - y0
    for p, q in ((-dx, x0 - box[0]), (dx, box[2] - x0), (-dy, y0 - box[1]), (dy, box[3] - y0)):
        if p == 0:
            if q < 0:
                return False
        elif p < 0:
            t0 = max(t0, q / p)
        else:
            t1 = min(t1, q / p)
        if t0 > t1:
            return False
    return True


def austria_cover(z, x, y):
    """Wie eine Kachel zu Oesterreich liegt: "in" (ganz, mit Abstand zur Grenze - mehr, als
    basemap.at an der Grenze ausblendet), "out" oder "edge" - danach richtet sich, welche
    Karte dort liegt. Gemerkt je Kachel."""
    key = (z, x, y)
    cover = _COVER.get(key)
    if cover is None:
        west, south, east, north = tile_box(z, x, y)
        margin = max(COVER_MARGIN, (EDGE_BAND + 4) / float(TILE_PX) * (east - west) + BORDER_ERROR)
        box = (west - margin, south - margin, east + margin, north + margin)
        if box[2] < AUSTRIA_BOX[0] or box[0] > AUSTRIA_BOX[2] or box[3] < AUSTRIA_BOX[1] or box[1] > AUSTRIA_BOX[3]:
            cover = "out"
        elif any(segment_in_box(ax, ay, bx, by, box) for ax, ay, bx, by in AUSTRIA_EDGES):
            cover = "edge"
        else:                                   # keine Grenze in der Naehe: ganz drin oder ganz draussen
            cover = "in" if in_rings(AUSTRIA_RINGS, (west + east) / 2, (south + north) / 2) else "out"
        if len(_COVER) > 50000:
            _COVER.clear()
        _COVER[key] = cover
    return cover


def edge_numpy():
    """numpy fuer die weichen Randkacheln laden - ohne (Paket python3-numpy) bleibt der harte
    Rand mit dem lila Grenzsaum von basemap.at."""
    global np
    if np is None:
        try:
            import numpy
            np = numpy
        except ImportError:
            np = False
    return np is not False


def pixbuf_rgba(pixbuf):
    """Ein Pixbuf als (Hoehe, Breite, 4) uint8 RGBA."""
    n, h, w, stride = pixbuf.get_n_channels(), pixbuf.get_height(), pixbuf.get_width(), pixbuf.get_rowstride()
    raw = np.frombuffer(pixbuf.get_pixels(), "uint8")
    raw = np.pad(raw, (0, max(0, h * stride - raw.size)))[:h * stride]     # die letzte Zeile ist kuerzer
    px = raw.reshape(h, stride)[:, :w * n].reshape(h, w, n)
    if n == 3:
        px = np.concatenate([px, np.full((h, w, 1), 255, "uint8")], axis=2)
    return px


def inside_distance(alpha, limit):
    """Abstand jedes Pixels zum naechsten durchsichtigen (Deckkraft unter 1/2) in px, hoechstens
    limit - achteckig genaehert, auf halber Aufloesung gerechnet und bilinear verdoppelt. Hoehe
    und Breite muessen gerade sein."""
    h, w = alpha.shape
    inside = alpha.reshape(h // 2, 2, w // 2, 2).min(axis=(1, 3)) >= 0.5
    dist = np.full(inside.shape, float(limit), "float32")
    reach = ~inside
    dist[reach] = 0.0
    for k in range(1, int(math.ceil(limit / 2.0)) + 2):
        grow = reach.copy()
        grow[1:, :] |= reach[:-1, :]
        grow[:-1, :] |= reach[1:, :]
        grow[:, 1:] |= reach[:, :-1]
        grow[:, :-1] |= reach[:, 1:]
        if k % 2 == 0:                  # abwechselnd mit den Diagonalen: achteckig statt quadratisch
            grow[1:, 1:] |= reach[:-1, :-1]
            grow[1:, :-1] |= reach[:-1, 1:]
            grow[:-1, 1:] |= reach[1:, :-1]
            grow[:-1, :-1] |= reach[1:, 1:]
        dist[grow & ~reach] = 2.0 * k - 1.0
        reach = grow

    def double(a, axis):
        a = np.moveaxis(a, axis, 0)
        out = np.empty((2 * a.shape[0],) + a.shape[1:], a.dtype)
        out[0::2] = 0.75 * a + 0.25 * np.concatenate([a[:1], a[:-1]])
        out[1::2] = 0.75 * a + 0.25 * np.concatenate([a[1:], a[-1:]])
        return np.moveaxis(out, 0, axis)
    return np.minimum(double(double(dist, 0), 1), limit)


def edge_tile(px, alpha):
    """Eine Randkachel von basemap.at, die weich in OpenStreetMap auslaeuft: ihr lila Grenzsaum
    (bis EDGE_BAND px innen) verschwindet, die Flaechen blenden auf den letzten EDGE_FADE px aus.
    Schrift mit ihrem weissen Rand und dunkle Linien bleiben stehen - basemap.at schreibt
    Ortsnamen auch ueber die Grenze hinaus. px: die Kachel (RGBA), alpha: Deckkraft (0..1) mit
    den Nachbarn, EDGE_BAND + 4 px rundherum. -> (cairo-Flaeche, Puffer) - der Puffer muss
    leben, solange die Flaeche gebraucht wird."""
    import cairo
    pad = EDGE_BAND + 4
    dist = inside_distance(alpha, EDGE_BAND + 2)[pad:pad + 256, pad:pad + 256]
    t = np.clip(dist / EDGE_FADE, 0.0, 1.0)
    weight = t * t * (3 - 2 * t)
    red, green, blue = (px[..., k].astype("float32") for k in range(3))
    lilac = np.clip((np.minimum(blue - green, 2 * (red - green)) - 4) / 10.0, 0.0, 1.0)
    weight *= 1 - lilac * (dist <= EDGE_BAND)
    near = (0.299 * red + 0.587 * green + 0.114 * blue) < 110      # Schrift und dunkle Linien ...
    for _ in range(2):                                              # ... mit 2 px Rand
        grow = near.copy()
        grow[1:, :] |= near[:-1, :]
        grow[:-1, :] |= near[1:, :]
        grow[:, 1:] |= near[:, :-1]
        grow[:, :-1] |= near[:, 1:]
        near = grow
    weight = np.maximum(weight, near * (1 - lilac))
    cover = px[..., 3].astype("float32") / 255.0 * weight
    out = np.empty((256, 256, 4), "float32")
    out[..., 0], out[..., 1], out[..., 2], out[..., 3] = blue * cover, green * cover, red * cover, 255 * cover
    buf = bytearray((out + 0.5).astype("uint8").tobytes())
    return cairo.ImageSurface.create_for_data(buf, cairo.FORMAT_ARGB32, 256, 256, 1024), buf


def project(lon, lat):
    """WGS84 -> Weltkoordinaten (Web Mercator) bei Zoom 0, 0 bis 256."""
    x = (lon + 180.0) / 360.0 * TILE_PX
    s = min(max(math.sin(math.radians(lat)), -0.9999), 0.9999)
    return x, (0.5 - math.log((1 + s) / (1 - s)) / (4 * math.pi)) * TILE_PX


class TileCache:
    """Kartenkacheln: im Speicher (die letzten MEMORY), auf der Platte (TILE_MAX_AGE) und
    aus dem Netz (drei Threads, neueste Anfrage zuerst - der aktuelle Ausschnitt laedt
    vor dem, ueber den man nur hinweggezogen hat). Fertige Kacheln zeichnen die Karten neu."""

    MEMORY = 400
    WORKERS = 3

    def __init__(self):
        self.mem = collections.OrderedDict()    # Schluessel -> (Pixbuf oder None, Zeit)
        self.edges = collections.OrderedDict()  # (z, x, y) -> (Flaeche, Puffer, Nachbarn, die fehlten)
        self.pending = set()
        self.queue = []
        self.cond = threading.Condition()
        self.views = []
        self.key = None                         # TomTom-Schluessel fuer die Verkehrsebene
        self.started = False

    def tile_path(self, layer, z, x, y):
        if layer == "flow":                     # Verkehr nur im Speicher - er veraltet in Minuten
            return None
        return os.path.join(TILE_DIR, layer, str(z), str(x), "%d.%s" % (y, "jpeg" if layer == "hidpi" else "png"))

    def tile_url(self, layer, z, x, y):
        if layer == "flow":
            return TOMTOM_FLOW.format(z=z, x=x, y=y, key=urllib.parse.quote(self.key)) if self.key else None
        return TILE_URLS[layer][0].format(z=z, x=x, y=y)

    def get(self, layer, z, x, y):
        """Kachel aus dem Speicher; fehlt sie (oder ist sie alt), wird sie geholt."""
        key = (layer, z, x, y)
        item = self.mem.get(key)
        if item is not None:
            pixbuf, stamp = item
            age = time.time() - stamp
            if (pixbuf is not None and (layer != "flow" or age < FLOW_MAX_AGE)) or (pixbuf is None and age < TILE_RETRY):
                self.mem.move_to_end(key)
                return pixbuf
        self.request(key)
        return item[0] if item else None

    def peek(self, layer, z, x, y):
        item = self.mem.get((layer, z, x, y))
        return item[0] if item else None

    def peek_edge(self, z, x, y):
        got = self.edges.get((z, x, y))
        return got[0] if got else None

    def edge(self, z, x, y):
        """Die Randkachel (z, x, y) von basemap.at, weich auslaufend (edge_tile); None, solange
        sie fehlt. Die Grenze kann in den Nachbarn liegen - fehlt dort einer noch, gilt vorerst
        sein Rand wie der der Kachel; kommt er, wird neu gerechnet."""
        key = (z, x, y)
        got = self.edges.get(key)
        if got is not None:
            self.edges.move_to_end(key)
            return got[0]
        center = self.get("normal", z, x, y)
        if center is None:
            return None
        px = pixbuf_rgba(center)
        mosaic = np.pad(px[..., 3].astype("float32") / 255.0, 256, mode="edge")
        missing = set()
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                if not dx and not dy:
                    continue
                cover = austria_cover(z, x + dx, y + dy)
                if cover == "edge":
                    near = self.peek("normal", z, x + dx, y + dy)
                    if near is None:
                        missing.add((z, x + dx, y + dy))
                        continue
                    part = pixbuf_rgba(near)[..., 3].astype("float32") / 255.0
                else:
                    part = 1.0 if cover == "in" else 0.0
                mosaic[256 + 256 * dy:512 + 256 * dy, 256 + 256 * dx:512 + 256 * dx] = part
        pad = EDGE_BAND + 4
        surface, buf = edge_tile(px, mosaic[256 - pad:512 + pad, 256 - pad:512 + pad])
        self.edges[key] = (surface, buf, missing)
        while len(self.edges) > EDGE_MEMORY:
            self.edges.popitem(last=False)
        return surface

    def request(self, key):
        with self.cond:
            if key in self.pending:
                return
            self.pending.add(key)
            self.queue.append(key)
            while len(self.queue) > 160:        # weit weggezogen: Altes nicht mehr laden
                self.pending.discard(self.queue.pop(0))
            self.cond.notify()
        if not self.started:
            self.started = True
            for _ in range(self.WORKERS):
                threading.Thread(target=self.worker, daemon=True).start()
            threading.Thread(target=self.prune_disk, daemon=True).start()

    def worker(self):
        while True:
            with self.cond:
                while not self.queue:
                    self.cond.wait()
                key = self.queue.pop()
            try:
                pixbuf = self.load(*key)
            except (Offline, ServiceError, NoResult, GLib.Error, OSError) as exc:
                if not isinstance(exc, Offline):
                    log("map tile %s/%d/%d/%d: %s" % (key[0], key[1], key[2], key[3], exc))
                pixbuf = None
            GLib.idle_add(self.done, key, pixbuf)

    def load(self, layer, z, x, y):
        path = self.tile_path(layer, z, x, y)
        if path and os.path.exists(path) and time.time() - os.path.getmtime(path) < TILE_MAX_AGE:
            return GdkPixbuf.Pixbuf.new_from_file(path)
        url = self.tile_url(layer, z, x, y)
        if not url:
            return None
        data = request_raw(url, headers={"Accept": "image/png,image/jpeg,image/*"})
        loader = GdkPixbuf.PixbufLoader()
        loader.write(data)
        loader.close()
        if path:
            tmp = "%s.%d.tmp" % (path, threading.get_ident())
            try:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(tmp, "wb") as fh:
                    fh.write(data)
                os.replace(tmp, path)
            except OSError as exc:
                log("could not store a map tile: %s" % exc)
        return loader.get_pixbuf()

    def done(self, key, pixbuf):
        self.pending.discard(key)
        self.mem[key] = (pixbuf, time.time())
        self.mem.move_to_end(key)
        while len(self.mem) > self.MEMORY:
            self.mem.popitem(last=False)
        layer, z, x, y = key
        if layer == "normal":                   # Randkacheln, denen sie als Nachbar fehlte, neu rechnen
            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    got = self.edges.get((z, x + dx, y + dy))
                    if got is not None and (dx or dy) and (z, x, y) in got[2]:
                        del self.edges[(z, x + dx, y + dy)]
        for view in self.views:
            view.area.queue_draw()
        return GLib.SOURCE_REMOVE

    @staticmethod
    def prune_disk():
        """Kacheln, die laenger als TILE_MAX_AGE niemand gebraucht hat, loeschen."""
        limit = time.time() - TILE_MAX_AGE
        for root, _dirs, files in os.walk(TILE_DIR):
            for name in files:
                path = os.path.join(root, name)
                try:
                    if os.path.getmtime(path) < limit:
                        os.remove(path)
                except OSError:
                    pass


class MapView:
    """Die Karte: basemap.at, darueber die Strecke (Fahrt tuerkis, Fussweg gepunktet,
    Stau orange bis rot), Haltestellen, Start und Ziel. Mausrad zoomt, Ziehen
    verschiebt, Doppelklick zoomt hinein. inset: so breit verdeckt die schwebende
    Karte links - "ganze Strecke" rueckt die Strecke daneben."""

    def __init__(self, tiles):
        self.tiles = tiles
        tiles.views.append(self)
        self.area = Gtk.DrawingArea(hexpand=True, vexpand=True)
        self.area.set_size_request(320, 240)
        self.area.add_events(Gdk.EventMask.SCROLL_MASK | Gdk.EventMask.SMOOTH_SCROLL_MASK
                             | Gdk.EventMask.BUTTON_PRESS_MASK | Gdk.EventMask.BUTTON_RELEASE_MASK
                             | Gdk.EventMask.POINTER_MOTION_MASK)
        self.center = project(16.3725, 48.2083)
        self.zoom = 12.0
        self.legs, self.markers = [], []
        self.inset = 0
        self.drag = None
        self.traffic = False
        self.credits = set()            # welche Karten zuletzt zu sehen waren (Quellenangabe)
        self.want_fit = False
        self.follow = False             # folgt dem Inhalt (auch bei neuer Groesse), bis man selbst zieht
        self.fit_size = None
        self.size = (0, 0)
        if can_draw():
            self.area.connect("draw", self.on_draw)
            self.area.connect("scroll-event", self.on_scroll)
            self.area.connect("button-press-event", self.on_press)
            self.area.connect("button-release-event", self.on_release)
            self.area.connect("motion-notify-event", self.on_motion)
        self.area.connect("destroy", lambda _a: self in tiles.views and tiles.views.remove(self))

    # -- Inhalt

    def set_content(self, legs=None, markers=None, fit=True):
        """legs: [{"style": ride|walk|cycle|car|bike|alt, "coords": [(lon, lat)], "traffic": [...]}]
        (cycle: Rad vor einer Fahrt, alt: andere Autoroute), markers: [{"kind":
        start|end|stop|minor|home|sign, "coord": (lon, lat)}]"""
        self.legs, self.markers = legs or [], markers or []
        if fit:
            self.want_fit = True
            self.follow = True
        self.area.queue_draw()

    def set_traffic(self, on):
        self.traffic = on
        self.area.queue_draw()

    def bounds(self):
        points = [project(*c) for leg in self.legs for c in leg["coords"]] \
            + [project(*m["coord"]) for m in self.markers if m.get("fit", True)]
        if not points:
            return None
        xs, ys = zip(*points)
        return min(xs), min(ys), max(xs), max(ys)

    def fit(self):
        """Ganze Strecke zeigen - im freien Teil rechts der schwebenden Karte."""
        width, height = self.size
        box = self.bounds()
        if not box or width < 80 or height < 80:
            self.want_fit = True
            return
        pad = 44
        # rechts der schwebenden Karte - ausser die Karte ist dafuer zu schmal
        left = self.inset + pad if width - self.inset - 2 * pad >= 220 else pad
        free_w, free_h = max(80, width - left - pad), max(80, height - 2 * pad)
        span_x, span_y = max(box[2] - box[0], 1e-7), max(box[3] - box[1], 1e-7)
        self.zoom = max(MAP_MIN_Z, min(FIT_MAX_Z, math.log2(min(free_w / span_x, free_h / span_y))))
        scale = 2 ** self.zoom
        mid_x, mid_y = (box[0] + box[2]) / 2, (box[1] + box[3]) / 2
        self.center = (mid_x - (left + free_w / 2 - width / 2) / scale, mid_y)
        self.want_fit = False
        self.follow = True
        self.fit_size = self.size
        self.area.queue_draw()

    def zoom_at(self, delta, x=None, y=None):
        """Zoomen, der Punkt unter dem Zeiger bleibt stehen."""
        self.follow = False
        width, height = self.size
        x = width / 2 if x is None else x
        y = height / 2 if y is None else y
        old = 2 ** self.zoom
        world = (self.center[0] + (x - width / 2) / old, self.center[1] + (y - height / 2) / old)
        self.zoom = max(MAP_MIN_Z, min(MAP_MAX_Z, self.zoom + delta))
        new = 2 ** self.zoom
        self.center = (world[0] - (x - width / 2) / new, world[1] - (y - height / 2) / new)
        self.area.queue_draw()

    # -- Zeichnen

    def screen(self, lon, lat):
        x, y = project(lon, lat)
        scale = 2 ** self.zoom
        width, height = self.size
        return (x - self.center[0]) * scale + width / 2, (y - self.center[1]) * scale + height / 2

    def on_draw(self, area, cr):
        self.size = (area.get_allocated_width(), area.get_allocated_height())
        if self.want_fit or (self.follow and self.size != self.fit_size):
            self.fit()
        self.draw_base(cr, area.get_scale_factor() > 1)
        if self.traffic and self.tiles.key:
            for tile in self.visible_tiles():
                self.paint_layer(cr, "flow", *tile)
        self.draw_route(cr)
        self.draw_markers(cr)
        self.draw_attribution(cr)
        return False

    def visible_tiles(self):
        """Die Kacheln im Ausschnitt: (Zoom, x, y, links, oben, Kantenlaenge am Bildschirm)."""
        width, height = self.size
        tz = max(0, min(MAP_MAX_Z, int(round(self.zoom))))
        count = 2 ** tz
        scale = 2 ** self.zoom
        side = TILE_PX / count * scale          # Kachel auf dem Bildschirm, logische Pixel
        world = TILE_PX / float(count)
        first_x = int(math.floor((self.center[0] - width / 2 / scale) / world))
        last_x = int(math.floor((self.center[0] + width / 2 / scale) / world))
        first_y = max(0, int(math.floor((self.center[1] - height / 2 / scale) / world)))
        last_y = min(count - 1, int(math.floor((self.center[1] + height / 2 / scale) / world)))
        for ty in range(first_y, last_y + 1):
            for tx in range(first_x, last_x + 1):
                yield (tz, tx % count, ty, (tx * world - self.center[0]) * scale + width / 2,
                       (ty * world - self.center[1]) * scale + height / 2, side)

    def draw_base(self, cr, hidpi):
        """Die Grundkarte: in Oesterreich basemap.at, rundherum OpenStreetMap, an der
        Grenze beide uebereinander - basemap.at ist ausserhalb durchsichtig und laeuft mit
        numpy ohne seinen lila Grenzsaum weich aus (edge_tile). Die HiDPI-Kacheln sind
        ausserhalb weiss, also an der Grenze die normalen."""
        cr.set_source_rgb(*MAP_BG)
        cr.paint()
        used = set()
        soft = edge_numpy()
        for tz, x, y, left, top, side in self.visible_tiles():
            cover = austria_cover(tz, x, y)
            if cover != "in":
                self.paint_layer(cr, "osm", tz, x, y, left, top, side)
                used.add("osm")
            if cover != "out":
                layer = "hidpi" if hidpi and cover == "in" else "edge" if cover == "edge" and soft else "normal"
                self.paint_layer(cr, layer, tz, x, y, left, top, side)
                used.add("basemap")
        self.credits = used

    def paint_layer(self, cr, layer, tz, x, y, left, top, side):
        """Eine Kachel - fehlt sie noch, die groebere darueber, vergroessert. "edge" ist die
        weich auslaufende Randkachel von basemap.at."""
        pixbuf = self.tiles.edge(tz, x, y) if layer == "edge" else self.tiles.get(layer, tz, x, y)
        if pixbuf is not None:
            self.paint_tile(cr, pixbuf, left, top, side, 0, 0, 1)
            return
        for up in range(1, 5):
            if tz - up < 0:
                break
            parent = (self.tiles.peek_edge(tz - up, x >> up, y >> up) if layer == "edge"
                      else self.tiles.peek(layer, tz - up, x >> up, y >> up))
            if parent is not None:
                part = 2 ** up
                self.paint_tile(cr, parent, left, top, side, x % part, y % part, part)
                break

    @staticmethod
    def paint_tile(cr, image, left, top, side, sub_x, sub_y, parts):
        """Kachel (oder ihr Teil sub_x/sub_y von parts x parts) auf side x side Pixel - ein
        Pixbuf oder eine cairo-Flaeche (Randkachel)."""
        cr.save()
        cr.rectangle(left, top, side + 0.5, side + 0.5)
        cr.clip()
        factor = side * parts / image.get_width()
        cr.translate(left - sub_x * side, top - sub_y * side)
        cr.scale(factor, factor)
        if isinstance(image, GdkPixbuf.Pixbuf):
            Gdk.cairo_set_source_pixbuf(cr, image, 0, 0)
        else:
            cr.set_source_surface(image, 0, 0)
        cr.paint()
        cr.restore()

    def polyline(self, cr, coords):
        points = [self.screen(*c) for c in coords]
        cr.new_path()
        cr.move_to(*points[0])
        for point in points[1:]:
            cr.line_to(*point)

    def draw_route(self, cr):
        import cairo
        accent = theme_color(self.area.get_style_context(), "accent_color", (0.39, 0.82, 0.87))
        cr.set_line_join(cairo.LINE_JOIN_ROUND)
        cr.set_line_cap(cairo.LINE_CAP_ROUND)
        for leg in self.legs:                   # andere Autorouten: grau, unter allem anderen
            if len(leg["coords"]) >= 2 and leg["style"] == "alt":
                self.polyline(cr, leg["coords"])
                cr.set_source_rgba(*ROUTE_EDGE, 0.35)
                cr.set_line_width(8)
                cr.stroke_preserve()
                cr.set_source_rgba(*ALT_RGB, 0.95)
                cr.set_line_width(5)
                cr.stroke()
        legs = [leg for leg in self.legs if leg["style"] != "alt" and len(leg["coords"]) >= 2]
        for leg in legs:                        # erst alle Raender, dann die Linien - Kreuzungen sauber
            if leg["style"] != "walk":
                self.polyline(cr, leg["coords"])
                cr.set_source_rgba(*ROUTE_EDGE, 0.85)
                cr.set_line_width(9)
                cr.stroke()
        for leg in legs:
            self.polyline(cr, leg["coords"])
            if leg["style"] == "cycle":         # Rad vor der Fahrt: tuerkis-weiss gestrichelt
                cr.set_source_rgba(1, 1, 1, 0.95)
                cr.set_line_width(5.5)
                cr.stroke_preserve()
                cr.set_dash([9, 6])
                cr.set_source_rgba(accent.red, accent.green, accent.blue, 1)
                cr.stroke()
                cr.set_dash([])
                continue
            if leg["style"] == "walk":          # Fussweg: einzelne Punkte, weiss umrandet, mit Luecken
                cr.set_dash([0.01, WALK_STEP - 0.01])
                cr.set_source_rgba(1, 1, 1, 0.95)
                cr.set_line_width(8)
                cr.stroke_preserve()
                cr.set_source_rgba(0.22, 0.24, 0.26, 1)
                cr.set_line_width(4.5)
                cr.stroke()
                cr.set_dash([])
                continue
            cr.set_source_rgba(accent.red, accent.green, accent.blue, 1)
            cr.set_line_width(5.5)
            cr.stroke()
            for jam in leg.get("traffic") or []:
                if len(jam["coords"]) < 2:
                    continue
                self.polyline(cr, jam["coords"])
                level = 4 if jam.get("category") == "ROAD_CLOSURE" else max(1, min(4, jam.get("magnitude") or 1))
                cr.set_source_rgb(*TRAFFIC_RGB[level])
                cr.set_line_width(5.5)
                cr.stroke()

    def draw_markers(self, cr):
        accent = theme_color(self.area.get_style_context(), "accent_color", (0.39, 0.82, 0.87))
        order = {"minor": 0, "stop": 1, "sign": 2, "home": 3, "start": 4, "end": 5}
        for marker in sorted(self.markers, key=lambda m: order.get(m["kind"], 0)):
            x, y = self.screen(*marker["coord"])
            kind = marker["kind"]
            if kind == "minor":
                if self.zoom < 13:
                    continue
                cr.arc(x, y, 3, 0, 2 * math.pi)
                cr.set_source_rgb(1, 1, 1)
                cr.fill_preserve()
                cr.set_source_rgba(*ROUTE_EDGE, 0.9)
                cr.set_line_width(1.5)
                cr.stroke()
            elif kind == "stop":
                self.ring(cr, x, y, 5.5, (1, 1, 1), (accent.red, accent.green, accent.blue), 3)
            elif kind == "start":
                self.ring(cr, x, y, 7.5, (0.11, 0.11, 0.11), (1, 1, 1), 3)
            elif kind == "end":
                self.ring(cr, x, y, 8.5, (accent.red, accent.green, accent.blue), (1, 1, 1), 3)
                cr.arc(x, y, 3, 0, 2 * math.pi)
                cr.set_source_rgb(1, 1, 1)
                cr.fill()
            elif kind == "sign":                # oesterreichisches Haltestellenschild
                self.ring(cr, x, y, 9, SIGN_YELLOW, (1, 1, 1), 2)
                cr.set_source_rgb(*SIGN_GREEN)
                cr.set_line_width(2)
                cr.move_to(x - 3, y - 4)
                cr.line_to(x - 3, y + 4)
                cr.move_to(x + 3, y - 4)
                cr.line_to(x + 3, y + 4)
                cr.move_to(x - 3, y)
                cr.line_to(x + 3, y)
                cr.stroke()
            elif kind == "home":
                self.ring(cr, x, y, 10, (0.11, 0.11, 0.11), (1, 1, 1), 2.5)
                pixbuf = glyph_pixbuf("home", 24, Gdk.RGBA(1, 1, 1, 1))
                if pixbuf is not None:
                    cr.save()
                    cr.translate(x - 6, y - 6.5)
                    cr.scale(0.5, 0.5)
                    Gdk.cairo_set_source_pixbuf(cr, pixbuf, 0, 0)
                    cr.paint()
                    cr.restore()

    @staticmethod
    def ring(cr, x, y, radius, fill, edge, width):
        cr.arc(x, y, radius, 0, 2 * math.pi)
        cr.set_source_rgb(*fill)
        cr.fill_preserve()
        cr.set_source_rgb(*edge)
        cr.set_line_width(width)
        cr.stroke()

    def draw_attribution(self, cr):
        width, height = self.size
        names = [MAP_CREDITS[k] for k in ("basemap", "osm") if k in self.credits]
        text = ("Map: " + ", ".join(names) if names else "") \
            + (" · Traffic: TomTom" if self.traffic and self.tiles.key else "")
        if not text:
            return
        layout = self.area.create_pango_layout(text)
        desc = self.area.get_pango_context().get_font_description().copy()
        desc.set_size(int(desc.get_size() * 0.78))
        layout.set_font_description(desc)
        tw, th = layout.get_pixel_size()
        x, y = width - tw - 10, height - th - 6
        cr.rectangle(x - 6, y - 2, tw + 12, th + 4)
        cr.set_source_rgba(1, 1, 1, 0.78)
        cr.fill()
        cr.set_source_rgba(0.15, 0.15, 0.15, 1)
        cr.move_to(x, y)
        PangoCairo.show_layout(cr, layout)

    # -- Maus

    def on_scroll(self, _area, event):
        delta = 0.0
        if event.direction == Gdk.ScrollDirection.UP:
            delta = 0.5
        elif event.direction == Gdk.ScrollDirection.DOWN:
            delta = -0.5
        elif event.direction == Gdk.ScrollDirection.SMOOTH:
            found, _dx, dy = event.get_scroll_deltas()
            delta = -dy * 0.35 if found else 0.0
        if delta:
            self.zoom_at(delta, event.x, event.y)
        return True

    def on_press(self, area, event):
        if event.button != 1:
            return False
        if event.type == getattr(Gdk.EventType, "DOUBLE_BUTTON_PRESS", getattr(Gdk.EventType, "_2BUTTON_PRESS", None)):
            self.drag = None
            self.zoom_at(1.0, event.x, event.y)
            return True
        self.drag = (event.x, event.y, self.center)
        window = area.get_window()
        if window is not None:
            window.set_cursor(Gdk.Cursor.new_from_name(area.get_display(), "grabbing"))
        return True

    def on_motion(self, _area, event):
        if self.drag is None:
            return False
        x0, y0, center = self.drag
        self.follow = False
        scale = 2 ** self.zoom
        self.center = (center[0] - (event.x - x0) / scale, center[1] - (event.y - y0) / scale)
        self.area.queue_draw()
        return True

    def on_release(self, area, event):
        if event.button == 1 and self.drag is not None:
            self.drag = None
            window = area.get_window()
            if window is not None:
                window.set_cursor(None)
        return False


def map_buttons(view, traffic_toggle=None):
    """Knoepfe rechts oben auf der Karte: hinein, heraus, ganze Strecke, Verkehr."""
    box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6, halign=Gtk.Align.END, valign=Gtk.Align.START)
    box.set_margin_top(12)
    box.set_margin_end(12)
    for key, tip, callback in (("plus", "Zoom in", lambda _b: view.zoom_at(1.0)),
                               ("minus", "Zoom out", lambda _b: view.zoom_at(-1.0)),
                               ("fit", "Show the whole route", lambda _b: view.fit())):
        button = styled(Gtk.Button(), "tr-mapbtn")
        button.add(icon(key, 16))
        button.set_tooltip_text(tip)
        button.connect("clicked", callback)
        box.pack_start(button, False, False, 0)
    toggle = None
    if traffic_toggle is not None:
        toggle = styled(Gtk.ToggleButton(), "tr-mapbtn")
        toggle.add(icon("traffic", 16))
        toggle.set_tooltip_text("Live traffic (TomTom)")
        toggle.connect("toggled", traffic_toggle)
        box.pack_start(toggle, False, False, 0)
    return box, toggle


# ------------------------------------------------------------------ Fenster: Route und Abfahrten

class TransitWindow:
    """Routenplaner und Abfahrten in einem Fenster, oben umschaltbar. Links Suche und
    Liste, rechts der Verlauf des gewaehlten Eintrags Schritt fuer Schritt."""

    def __init__(self, tray, page="route"):
        prepare_ui()
        self.tray = tray
        self.serial = 0                 # zaehlt Suchen - nur die Antworten auf die letzte zaehlen
        self.mode = "transit"
        self.results = {}               # Verkehrsmittel -> Ergebnis oder Ausnahme
        self.searched = None            # (Start, Ziel, Zeit) der laufenden Suche
        self.paging = False
        self.list_items = []            # was je Zeile der Routenliste steht
        self.leave_labels = []          # (Label, Verbindung) - "leave in 3 min" wandert mit
        self.dep_items = []             # Abfahrt je Zeile der Abfahrtsliste
        self.dep_shape = None           # was die Abfahrtsliste zuletzt zeigte
        self.selected_dep = None
        self.trip_serial = 0
        self.traffic_toggles = []
        self.views = []
        self.line_filter = None         # offenes Filter-Popover einer Haltestelle
        self.editing = False            # gespeicherte Ziele bearbeiten (Startliste)
        self.cleared = None             # die letzten Ziele vor "Clear", fuer "Undo"

        win = self.window = Gtk.Window(title="Transit")
        win.set_default_size(1180, 720)
        win.connect("destroy", self.on_destroy)
        win.connect("key-press-event", self.on_key)
        win.set_icon_name(APP_ICON)
        bar = Gtk.HeaderBar(show_close_button=True)
        logo = Gtk.Image.new_from_icon_name(APP_ICON, Gtk.IconSize.LARGE_TOOLBAR)
        logo.set_pixel_size(22)
        bar.pack_start(logo)
        self.stack = Gtk.Stack(transition_type=Gtk.StackTransitionType.CROSSFADE)
        switcher = Gtk.StackSwitcher(stack=self.stack)
        bar.set_custom_title(switcher)
        refresh = Gtk.Button.new_from_icon_name("view-refresh-symbolic", Gtk.IconSize.BUTTON)
        refresh.set_tooltip_text("Refresh")
        refresh.connect("clicked", self.on_refresh)
        bar.pack_end(refresh)
        win.set_titlebar(bar)
        self.stack.add_titled(self.build_route_page(), "route", "Route")
        self.stack.add_titled(self.build_departures_page(), "departures", "Departures")
        self.stack.connect("notify::visible-child-name", self.on_page)
        win.add(self.stack)
        win.show_all()
        self.time_box.set_visible(False)
        self.paging_box.set_visible(False)
        self.update_traffic_buttons()
        self.update_star()

        home = tray.settings.get("home")
        if home:
            self.from_entry.set_place(dict(home, name="Home"), "Home")
        self.show_list()
        self.show_page(page)
        self.departures_changed()
        self.tick = GLib.timeout_add_seconds(30, self.on_tick)
        if page == "route":
            (self.to_entry if home else self.from_entry).entry.grab_focus()

    # -- Aufbau

    def build_route_page(self):
        page = styled(Gtk.Box(spacing=14), "tr-body")
        left = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=10)
        left.set_size_request(LEFT_W, -1)
        left.set_hexpand(False)         # sonst erbt die Spalte "ausdehnen" von den Eingabefeldern

        places = styled(Gtk.Grid(column_spacing=8, row_spacing=0), "tr-card", "tr-places")
        self.from_entry = PlaceEntry(self, "From")
        self.to_entry = PlaceEntry(self, "Where to?")
        self.from_icon = Glyph("home", 16, "dim-label")
        places.attach(self.from_icon.widget, 0, 0, 1, 1)
        places.attach(self.from_entry.entry, 1, 0, 1, 1)
        places.attach(styled(Gtk.Box(), "tr-rule"), 1, 1, 1, 1)
        places.attach(icon("pin", 16, "dim-label"), 0, 2, 1, 1)
        to_row = Gtk.Box(spacing=2)
        to_row.pack_start(self.to_entry.entry, True, True, 0)
        self.star_glyph = Glyph("star", 14)
        self.star = styled(Gtk.Button(), "tr-order")
        self.star.add(self.star_glyph.widget)
        self.star.set_valign(Gtk.Align.CENTER)
        when_clicked(self.star, self.on_star)
        to_row.pack_start(self.star, False, False, 0)
        places.attach(to_row, 1, 2, 1, 1)
        swap = Gtk.Button()
        swap.add(icon("swap", 16))
        swap.set_relief(Gtk.ReliefStyle.NONE)
        swap.set_valign(Gtk.Align.CENTER)
        swap.set_tooltip_text("Swap start and destination")
        swap.connect("clicked", self.on_swap)
        places.attach(swap, 2, 0, 1, 3)
        left.pack_start(places, False, False, 0)

        timing = Gtk.Box(spacing=6)
        self.when = Gtk.ComboBoxText()
        for text in ("Leave now", "Depart at", "Arrive by"):
            self.when.append_text(text)
        self.when.set_active(0)
        self.when.connect("changed", self.on_when)
        timing.pack_start(self.when, False, False, 0)
        self.time_box = Gtk.Box(spacing=6)
        self.day = Gtk.ComboBoxText()
        today = dt.date.today()
        for n in range(7):
            day = today + dt.timedelta(days=n)
            self.day.append_text("Today" if n == 0 else "Tomorrow" if n == 1
                                 else "%s %d %s" % (DAYS[day.weekday()], day.day, MONTHS[day.month - 1]))
        self.day.set_active(0)
        self.day.connect("changed", lambda _c: self.search_soon())
        self.clock = Gtk.Entry(width_chars=6, max_length=5, placeholder_text="18:30")
        self.clock.connect("changed", lambda _e: self.search_soon(700))
        self.clock.connect("activate", lambda _e: self.search())
        self.time_box.pack_start(self.day, False, False, 0)
        self.time_box.pack_start(self.clock, False, False, 0)
        timing.pack_start(self.time_box, False, False, 0)
        left.pack_start(timing, False, False, 0)

        # Fuenf Knoepfe passen nur mit der Dauer unter dem Symbol in die Spalte
        modes = Gtk.Box(spacing=4, homogeneous=True)
        self.mode_buttons, self.mode_labels, group = {}, {}, None
        for mode, keys, name in MODES:
            button = styled(Gtk.RadioButton.new_from_widget(group), "tr-mode")
            button.set_mode(False)              # als Knopf, ohne Auswahlpunkt
            group = group or button
            box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2, halign=Gtk.Align.CENTER)
            glyphs = Gtk.Box(spacing=1, halign=Gtk.Align.CENTER)
            for key in keys:
                glyphs.pack_start(icon(key, 16), False, False, 0)
            box.pack_start(glyphs, False, False, 0)
            self.mode_labels[mode] = label("–", "tr-sub", xalign=0.5)
            box.pack_start(self.mode_labels[mode], False, False, 0)
            button.add(box)
            button.set_tooltip_text(name)
            button.connect("toggled", self.on_mode, mode)
            modes.pack_start(button, True, True, 0)
            self.mode_buttons[mode] = button
        left.pack_start(modes, False, False, 0)

        scroller = Gtk.ScrolledWindow(hscrollbar_policy=Gtk.PolicyType.NEVER,
                                      vscrollbar_policy=Gtk.PolicyType.AUTOMATIC)
        self.route_list = styled(Gtk.ListBox(selection_mode=Gtk.SelectionMode.SINGLE), "tr-list")
        self.route_list.connect("row-selected", self.on_route_selected)
        self.route_list.connect("row-activated", self.on_route_activated)
        scroller.add(self.route_list)
        frame = styled(Gtk.Box(), "tr-card")
        frame.pack_start(scroller, True, True, 0)
        left.pack_start(frame, True, True, 0)

        foot = Gtk.Box(spacing=6)
        self.paging_box = Gtk.Box(spacing=6)
        self.earlier = Gtk.Button(label="Earlier")
        self.earlier.connect("clicked", self.on_page_turn, "earlier")
        self.later = Gtk.Button(label="Later")
        self.later.connect("clicked", self.on_page_turn, "later")
        self.paging_box.pack_start(self.earlier, False, False, 0)
        self.paging_box.pack_start(self.later, False, False, 0)
        foot.pack_start(self.paging_box, False, False, 0)
        self.status = label("", "tr-sub", "dim-label", ellipsize=True)
        foot.pack_end(self.status, True, True, 0)
        self.status.set_xalign(1.0)
        left.pack_start(foot, False, False, 0)
        page.pack_start(left, False, False, 0)

        self.route_view, self.route_detail, side = self.map_side()
        page.pack_start(side, True, True, 0)
        return page

    def build_departures_page(self):
        page = styled(Gtk.Box(spacing=14), "tr-body")
        left = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=10)
        left.set_size_request(LEFT_W, -1)
        left.set_hexpand(False)         # sonst erbt die Spalte "ausdehnen" von den Eingabefeldern
        scroller = Gtk.ScrolledWindow(hscrollbar_policy=Gtk.PolicyType.NEVER,
                                      vscrollbar_policy=Gtk.PolicyType.AUTOMATIC)
        self.dep_list = styled(Gtk.ListBox(selection_mode=Gtk.SelectionMode.SINGLE), "tr-list")
        self.dep_list.connect("row-selected", self.on_dep_selected)
        scroller.add(self.dep_list)
        frame = styled(Gtk.Box(), "tr-card")
        frame.pack_start(scroller, True, True, 0)
        left.pack_start(frame, True, True, 0)
        foot = Gtk.Box(spacing=6)
        home = Gtk.Button(label="Home & stops…")
        home.connect("clicked", lambda _b: self.tray.open_home())
        foot.pack_start(home, False, False, 0)
        self.dep_status = label("", "tr-sub", "dim-label", ellipsize=True)
        self.dep_status.set_xalign(1.0)
        foot.pack_end(self.dep_status, True, True, 0)
        left.pack_start(foot, False, False, 0)
        page.pack_start(left, False, False, 0)
        self.dep_view, self.dep_detail, side = self.map_side()
        page.pack_start(side, True, True, 0)
        return page

    def map_side(self):
        """Rechts: die Karte, darueber links schwebend der Verlauf, rechts oben die Knoepfe."""
        view = MapView(self.tray.tiles)
        view.inset = FLOAT_W + 12
        settings = self.tray.settings
        view.traffic = bool(settings.get("tomtom_key")) and settings.get("traffic_layer", True)
        self.views.append(view)
        overlay = Gtk.Overlay()
        overlay.add(view.area)
        card = styled(Gtk.Box(orientation=Gtk.Orientation.VERTICAL), "tr-float")
        card.set_size_request(FLOAT_W, -1)
        card.set_halign(Gtk.Align.START)
        card.set_valign(Gtk.Align.FILL)
        card.set_margin_top(12)
        card.set_margin_bottom(12)
        card.set_margin_start(12)
        detail = Detail(view, self)
        card.pack_start(detail.widget, True, True, 0)
        overlay.add_overlay(card)
        buttons, toggle = map_buttons(view, self.on_traffic)
        self.traffic_toggles.append(toggle)
        overlay.add_overlay(buttons)
        return view, detail, overlay

    def update_traffic_buttons(self):
        """Den Verkehrsknopf gibt es nur mit TomTom-Schluessel."""
        settings = self.tray.settings
        key = settings.get("tomtom_key")
        self.tray.tiles.key = key
        on = bool(key) and settings.get("traffic_layer", True)
        for toggle in self.traffic_toggles:
            toggle.set_visible(bool(key))
            if toggle.get_active() != on:
                toggle.set_active(on)
        for view in self.views:
            view.set_traffic(on)

    def on_traffic(self, toggle):
        on = toggle.get_active()
        if on == self.tray.settings.get("traffic_layer", True) and all(v.traffic == on for v in self.views):
            return
        self.tray.settings["traffic_layer"] = on
        save_settings(self.tray.settings)
        for other in self.traffic_toggles:
            if other is not toggle and other.get_active() != on:
                other.set_active(on)
        for view in self.views:
            view.set_traffic(on)

    def warning_hex(self):
        rgba = theme_color(self.window.get_style_context(), "warning_color", (1.0, 0.64, 0.49))
        return "#%02x%02x%02x" % tuple(int(round(c * 255)) for c in (rgba.red, rgba.green, rgba.blue))

    # -- Seiten

    def show_page(self, page):
        self.stack.set_visible_child_name(page)

    def on_page(self, _stack, _param):
        if self.stack.get_visible_child_name() == "departures":
            self.departures_changed()
            cache = self.tray.cache
            if cache and time.time() - cache["fetched_at"] > POLL_WINDOW:
                self.tray.refresh()

    def showing_departures(self):
        return self.stack.get_visible_child_name() == "departures" and self.window.is_active()

    def on_refresh(self, _button):
        if self.stack.get_visible_child_name() == "departures":
            self.tray.refresh()
        else:
            self.search()

    # -- Start, Ziel, Zeit

    def place_chosen(self, entry, place, is_home=False):
        if entry is self.from_entry:
            self.from_icon.set("home" if is_home else "pin")
            if not self.to_entry.place:
                self.to_entry.entry.grab_focus()
        elif not is_home:
            self.tray.remember(place)
        self.update_star()
        self.search()

    def place_cleared(self, entry):
        """Im Feld wird getippt. Ist das Ziel ganz geloescht, gehen auch seine Ergebnisse -
        die Liste zeigt wieder die gespeicherten und letzten Ziele."""
        if entry is self.from_entry:
            self.from_icon.set("pin")
            return
        self.update_star()
        if self.searched and not entry.entry.get_text().strip():
            self.search()

    def place_left(self, entry):
        """Feld verlassen ohne Treffer zu waehlen: alten Ort wiederherstellen? Nein -
        das Feld bleibt, wie es ist; gesucht wird erst mit einem gewaehlten Ort."""
        if entry is self.to_entry and not entry.entry.get_text().strip() and self.searched:
            self.search()

    def home_changed(self):
        """Zuhause neu gewaehlt: steht im Start "Home", gilt das neue."""
        home = self.tray.settings.get("home")
        if home and (self.from_entry.place is None or self.from_entry.entry.get_text() == "Home"):
            self.from_entry.set_place(dict(home, name="Home"), "Home")
            self.from_icon.set("home")
            self.search()
        self.update_star()
        self.departures_changed()

    def on_swap(self, _button):
        a, b = self.from_entry.place, self.to_entry.place
        a_text, b_text = self.from_entry.entry.get_text(), self.to_entry.entry.get_text()
        self.from_entry.set_place(b, b_text)
        self.to_entry.set_place(a, a_text)
        self.from_icon.set("home" if b_text == "Home" else "pin")
        self.update_star()
        self.search()

    def on_when(self, combo):
        self.time_box.set_visible(combo.get_active() > 0)
        if combo.get_active() > 0 and not self.clock.get_text().strip():
            soon = dt.datetime.now(self.origin_zone()) + dt.timedelta(minutes=15)
            soon -= dt.timedelta(minutes=soon.minute % 5)
            self.clock.set_text("%02d:%02d" % (soon.hour, soon.minute))
            self.clock.grab_focus()
        self.search()

    def when_time(self):
        """(Zeit, Ankunft?) oder None fuer jetzt; "invalid" bei unlesbarer Uhrzeit."""
        index = self.when.get_active()
        if index <= 0:
            return None
        found = re.match(r"^\s*(\d{1,2})(?:[:.h ]?(\d{2}))?\s*$", self.clock.get_text())
        hour, minute = (int(found.group(1)), int(found.group(2) or 0)) if found else (99, 99)
        if hour > 23 or minute > 59:
            self.clock.get_style_context().add_class("error")
            return "invalid"
        self.clock.get_style_context().remove_class("error")
        tz = self.origin_zone()
        day = dt.datetime.now(tz).date() + dt.timedelta(days=max(0, self.day.get_active()))
        return dt.datetime(day.year, day.month, day.day, hour, minute, tzinfo=tz).timestamp(), index == 2

    def origin_zone(self):
        """Die eingegebene Uhrzeit gilt am Start - in Lissabon eine Stunde frueher als in Wien."""
        place = self.from_entry.place
        return zone(place.get("tz") if place else None)

    def search_soon(self, delay=300):
        if getattr(self, "search_timer", None):
            GLib.source_remove(self.search_timer)
        self.search_timer = GLib.timeout_add(delay, self.on_search_timer)

    def on_search_timer(self):
        self.search_timer = None
        self.search()
        return GLib.SOURCE_REMOVE

    # -- Suche

    def search(self):
        """Alle Verkehrsmittel auf einmal suchen: Oeffis beim zustaendigen Planer, Rad +
        Oeffis bei Transitous, Rad, zu Fuss und Auto bei TomTom bzw. OSRM - jedes Ergebnis
        kommt fuer sich an."""
        origin, destination = self.from_entry.place, self.to_entry.place
        moment = self.when_time()
        self.serial += 1
        self.results = {}
        if not origin or not destination or moment == "invalid":
            self.searched = None
            self.show_list()
            return
        self.searched = (origin, destination, moment)
        self.editing, self.cleared = False, None
        for mode in self.mode_buttons:
            self.mode_labels[mode].set_text("…")
        self.status.set_text("Searching…")
        self.show_list()
        threading.Thread(target=self.fetch_transit, args=(self.serial, origin, destination, moment, None, None),
                         daemon=True).start()
        threading.Thread(target=self.fetch_mixed, args=(self.serial, origin, destination, moment),
                         daemon=True).start()
        for mode in ("bike", "walk", "car"):
            threading.Thread(target=self.fetch_direct, args=(self.serial, mode, origin, destination, moment),
                             daemon=True).start()

    def fetch_transit(self, serial, origin, destination, moment, context, direction, planner=None):
        try:
            result = transit_search(origin, destination, moment, context, planner)
        except (NoResult, Offline) as exc:
            result = exc
        except Exception as exc:  # noqa: BLE001
            log("connection search failed: %s: %s" % (type(exc).__name__, exc))
            result = ServiceError("The search did not work - try again later.")
        GLib.idle_add(self.got_transit, serial, result, direction)

    def fetch_mixed(self, serial, origin, destination, moment):
        try:
            result = mixed_search(origin, destination, moment)
        except (NoResult, Offline) as exc:
            result = exc
        except Exception as exc:  # noqa: BLE001
            log("bike + transit search failed: %s: %s" % (type(exc).__name__, exc))
            result = ServiceError("The search did not work - try again later.")
        GLib.idle_add(self.got_direct, serial, "mixed", result)

    def fetch_direct(self, serial, mode, origin, destination, moment=None):
        try:
            result = direct_route(mode, origin, destination, self.tray.settings.get("tomtom_key"), moment)
        except (NoResult, Offline) as exc:
            result = exc
        except Exception as exc:  # noqa: BLE001
            log("%s route failed: %s: %s" % (mode, type(exc).__name__, exc))
            result = ServiceError("No route right now - try again later.")
        GLib.idle_add(self.got_direct, serial, mode, result)

    def got_transit(self, serial, result, direction):
        if serial != self.serial or self.window is None:
            return GLib.SOURCE_REMOVE
        self.paging = False
        old = self.results.get("transit")
        if direction and isinstance(old, dict) and isinstance(result, dict):
            # Blaettern: dazunehmen, was neu ist
            known = {con_key(c) for c in old["cons"]}
            added = [c for c in result["cons"] if con_key(c) not in known]
            result = {"cons": old["cons"] + added, "planner": old.get("planner"),
                      "later": result["later"] if direction == "later" else old["later"],
                      "earlier": result["earlier"] if direction == "earlier" else old["earlier"]}
        elif direction and isinstance(old, dict):
            result = old                # beim Blaettern nichts mehr gefunden: bleiben
        self.results["transit"] = result
        self.after_result("transit")
        return GLib.SOURCE_REMOVE

    def got_direct(self, serial, mode, result):
        if serial != self.serial or self.window is None:
            return GLib.SOURCE_REMOVE
        self.results[mode] = result
        self.after_result(mode)
        return GLib.SOURCE_REMOVE

    # Was zu Oeffis und zu Rad + Oeffis gezeigt wird, haengt auch von den anderen ab
    DEPENDS = {"walk": ("transit", "mixed"), "transit": ("mixed",), "bike": ("mixed",)}

    def after_result(self, mode):
        for each in self.mode_labels:
            self.mode_labels[each].set_markup(self.mode_summary(each))
        self.update_status()
        if mode == self.mode or self.mode in self.DEPENDS.get(mode, ()):
            self.show_list(keep=True)

    def update_status(self):
        """Unten rechts: wer die Verbindungen rechnet, beim Suchen "Searching…"."""
        mode = self.mode if self.mode in ("transit", "mixed") else None
        result = self.results.get(mode) if mode else None
        if not self.searched or mode is None:
            text = "Searching…" if self.searched and self.results.get(self.mode) is None else ""
        elif result is None:
            text = "Searching…"
        elif isinstance(result, Exception):
            text = str(result) if mode == "transit" else ""
        else:
            text = "Route by %s · %s" % (SOURCE_NAMES.get(result.get("planner"), "ÖBB"), when(time.time(), time.time()))
        self.status.set_text(text)

    def found(self, mode):
        """Das Ergebnis eines Verkehrsmittels, wenn es eines gibt (sonst None)."""
        result = self.results.get(mode)
        return result if isinstance(result, dict) else None

    def transit_cons(self):
        """Die sinnvollen Verbindungen mit Oeffis und ein Hinweis, wenn keine bleibt - mit
        dem Vergleich zu Fuss, sobald dessen Route da ist."""
        result, walk = self.found("transit"), self.found("walk")
        if result is None:
            return [], None
        return sensible(result["cons"], walk["duration"] if walk else None)

    def mixed_cons(self):
        """Rad + Oeffis, die sich lohnen, und ein Hinweis, wenn keine. None, solange
        Oeffis oder Rad allein noch suchen - sonst tauchten Verbindungen auf und
        verschwaenden wieder."""
        result = self.found("mixed")
        if result is None:
            return [], None
        if self.results.get("transit") is None or self.results.get("bike") is None:
            return None, None
        transit = min((con_duration(c) for c in self.transit_cons()[0]), default=None)
        bike = self.found("bike")
        return sensible_mixed(result["cons"], transit, bike["duration"] if bike else result.get("bike"))

    def mode_summary(self, mode):
        """Dauer fuer den Umschalter: die schnellste sinnvolle Verbindung bzw. Route."""
        result = self.results.get(mode)
        if result is None:
            return "…" if self.searched else "–"
        if isinstance(result, Exception):
            return "–"
        if mode in ("transit", "mixed"):
            cons, _note = self.transit_cons() if mode == "transit" else self.mixed_cons()
            if cons is None:
                return "…"
            fastest = min((con_duration(c) for c in cons), default=None)
            return duration_text(fastest) if fastest is not None else "–"
        text = GLib.markup_escape_text(duration_text(result["duration"]))
        delay = int(round((result.get("delay") or 0) / 60.0))
        if result.get("live") and delay > 0:          # Stau: die Minuten dazu, orange
            text += ' <span foreground="%s" size="small">+%d</span>' % (self.warning_hex(), delay)
        return text

    def on_mode(self, button, mode):
        if button.get_active():
            self.mode = mode
            self.update_status()
            self.show_list()

    def on_page_turn(self, _button, direction):
        result = self.results.get("transit")
        if self.paging or not self.searched or not isinstance(result, dict) or not result.get(direction):
            return
        self.paging = True
        origin, destination, moment = self.searched
        self.status.set_text("Searching…")
        threading.Thread(target=self.fetch_transit, args=(self.serial, origin, destination, moment,
                                                          result[direction], direction, result.get("planner")),
                         daemon=True).start()

    # -- Liste links, Verlauf rechts

    def clear_list(self, listbox):
        for child in listbox.get_children():
            child.destroy()

    def list_content(self):
        """Was die Routenliste zeigt: ("start"|"wait"|"note", Text) oder ("items",
        [Eintrag], Hinweis) - Eintrag ("con", Verbindung) bzw. ("direct", Route, andere)."""
        if not self.searched:
            return ("start", None)
        result = self.results.get(self.mode)
        if result is None:
            return ("wait", "Searching…")
        if isinstance(result, Exception):
            return ("note", str(result))
        if self.mode in ("transit", "mixed"):
            cons, note = self.transit_cons() if self.mode == "transit" else self.mixed_cons()
            if cons is None:
                return ("wait", "Searching…")
            return ("items", [("con", c) for c in cons], note)
        routes = [result] + (result.get("alternatives") or [])
        return ("items", [("direct", r, [o for o in routes if o is not r]) for r in routes], None)

    @staticmethod
    def item_key(item):
        if item is None:
            return None
        if item[0] == "con":
            return ("con", con_key(item[1]))
        if item[0] == "direct":
            return ("direct", item[1]["mode"], round(item[1]["duration"]), round(item[1]["distance"]))
        return (item[0], (item[1] or {}).get("name"))

    def show_list(self, keep=False):
        """Die Routenliste fuer das gewaehlte Verkehrsmittel; ohne Suche die Ziele zur Wahl.
        keep: nur neu aufbauen, wenn sich etwas geaendert hat, und die Auswahl behalten -
        fuer Ergebnisse, die nachtraeglich ankommen (zu Fuss filtert die Oeffis mit)."""
        content = self.list_content()
        shape = (self.mode, content[0], content[1] if content[0] != "items" else
                 (tuple(self.item_key(i) for i in content[1]), content[2]))
        if keep and shape == getattr(self, "list_shape", None):
            return
        selected = self.item_at(self.route_list.get_selected_row()) if keep else None
        self.list_shape = shape
        self.clear_list(self.route_list)
        self.list_items, self.leave_labels = [], []
        transit = self.mode == "transit"
        result = self.results.get(self.mode)
        # Blaettern nur, wo es Verbindungen gibt - geht man besser zu Fuss, auch spaeter
        self.paging_box.set_visible(transit and isinstance(result, dict) and content[0] == "items"
                                    and bool(content[1]))
        if isinstance(result, dict) and transit:
            self.earlier.set_sensitive(bool(result.get("earlier")))
            self.later.set_sensitive(bool(result.get("later")))
        if content[0] == "start":
            for mode in self.mode_labels:
                self.mode_labels[mode].set_text("–")
            self.status.set_text("")
            self.show_start()
            return
        if content[0] in ("wait", "note"):
            self.add_note(self.route_list, content[1])
            self.route_detail.message(content[1])
            return
        items, note = content[1], content[2]
        if not items:
            self.add_note(self.route_list, note or "Nothing sensible found.")
            self.route_detail.message(note or "Nothing sensible found.")
            return
        now = time.time()
        prefix = self.tray.settings.get("prefix") or ""
        fastest = min(item[1]["duration"] for item in items) if items[0][0] == "direct" else None
        for item in items:
            if item[0] == "con":
                widget, leave = connection_row(item[1], prefix)
                self.leave_labels.append((leave, item[1]))
            else:
                widget = direct_row(item[1], self.direct_start(item[1]), fastest if len(items) > 1 else None)
            self.add_row(self.route_list, widget, item)
        self.update_leave(now)
        first = 0
        if items[0][0] == "con":
            first = next((i for i, item in enumerate(items) if eff_time(item[1], "dep") >= now - 60), 0)
        wanted = self.item_key(selected)
        first = next((i for i, item in enumerate(items) if wanted and self.item_key(item) == wanted), first)
        row = self.route_list.get_row_at_index(first)
        if row is not None:
            self.route_list.select_row(row)

    def show_start(self):
        """Ohne Suche die Ziele zur Wahl: oben die gespeicherten ("Edit": eigene Namen,
        Reihenfolge, entfernen), darunter die letzten - der Stern speichert eines, das
        Kreuz entfernt es, "Clear" leert die Liste (mit "Undo")."""
        settings = self.tray.settings
        saved, recent = settings.get("saved") or [], settings.get("recent") or []
        self.editing = self.editing and bool(saved)
        if not saved and not recent and self.cleared is None:
            self.add_note(self.route_list, "Type an address, a stop or a place. The star next to a destination "
                                           "keeps it here.")
        else:
            self.add_head("Saved", link_button("Done" if self.editing else "Edit", self.on_edit, self.editing)
                          if saved else None)
            if not saved:
                self.add_note(self.route_list, "The star next to a destination keeps it here.")
            for index, place in enumerate(saved):
                widget = self.saved_editor(place, index, len(saved)) if self.editing else place_row(place, "starred")
                self.add_row(self.route_list, widget, ("saved", place), activatable=not self.editing)
            if recent or self.cleared:
                self.add_head("Recent", link_button("Clear", self.on_clear) if recent else
                              link_button("Undo", self.on_undo))
            if not recent and self.cleared:
                self.add_note(self.route_list, "Recent destinations cleared.")
            full = len(saved) >= SAVED_MAX
            for place in recent:
                row = place_row(place, "clock")
                row.pack_end(tool_button("close", "Remove from recent destinations",
                                         lambda p=place: self.forget_recent(p)), False, False, 0)
                star = tool_button("star", "Save this destination", lambda p=place: self.save(p))
                star.set_sensitive(not full)
                if full:
                    star.set_tooltip_text("You can save up to %d destinations" % SAVED_MAX)
                row.pack_end(star, False, False, 0)
                self.add_row(self.route_list, row, ("recent", place))
            self.route_list.show_all()
        if self.editing:
            self.route_detail.message("Give your saved destinations your own names, order them with the arrows "
                                      "or remove them. “Done” or Esc when you are finished.")
        elif self.tray.settings.get("home"):
            self.route_detail.message("Where to? Type an address, a stop or a place above.")
        else:
            self.route_detail.message("Type a start and a destination above.\n\n"
                                      "Set your home under “Home & stops…” in the menu - then it is the start.")

    def add_head(self, text, button=None):
        """Ueberschrift in der Routenliste, rechts davon ein Textknopf."""
        head = styled(Gtk.ListBoxRow(activatable=False, selectable=False), "tr-head")
        box = Gtk.Box(spacing=6)
        box.pack_start(label(text, "tr-section", "tr-sub"), True, True, 0)
        if button is not None:
            box.pack_end(button, False, False, 0)
        head.add(box)
        self.route_list.add(head)
        self.list_items.append(None)

    def saved_editor(self, place, index, count):
        """Ein gespeichertes Ziel beim Bearbeiten: sein Name im Feld (leer = der Ortsname),
        darunter welcher Ort es ist; Pfeile ordnen, das Kreuz entfernt."""
        row = Gtk.Box(spacing=10)
        row.pack_start(icon("starred", 16, "dim-label"), False, False, 0)
        text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=3)
        name = styled(Gtk.Entry(text=place_title(place), placeholder_text=place["name"], max_length=LABEL_MAX,
                                width_chars=1, hexpand=True), "tr-rename")
        name.connect("changed", lambda entry: self.tray.rename_saved(place, entry.get_text()))
        name.connect("activate", lambda _entry: self.on_edit())
        text.pack_start(name, False, False, 0)
        where = " · ".join(t for t in (place["name"], place.get("sub")) if t)
        text.pack_start(label(where, "tr-sub", "dim-label", ellipsize=True), False, False, 0)
        row.pack_start(text, True, True, 0)
        tools = Gtk.Box(spacing=2)
        for key, step, tip in (("up", -1, "Move this destination up"), ("down", 1, "Move this destination down")):
            if count < 2:
                break
            button = tool_button(key, tip, lambda s=step: self.move_saved(index, s))
            button.set_sensitive(0 <= index + step < count)
            tools.pack_start(button, False, False, 0)
        tools.pack_start(tool_button("close", "Remove from saved destinations", lambda: self.unsave(place)),
                         False, False, 0)
        row.pack_end(tools, False, False, 0)
        return row

    def add_row(self, listbox, widget, item, activatable=True):
        row = Gtk.ListBoxRow(activatable=activatable)
        row.add(widget)
        listbox.add(row)
        row.show_all()
        if listbox is self.route_list:
            self.list_items.append(item)
        return row

    def add_note(self, listbox, text):
        row = Gtk.ListBoxRow(activatable=False, selectable=False)
        row.add(label(text, "dim-label", wrap=True))
        listbox.add(row)
        row.show_all()
        if listbox is self.route_list:
            self.list_items.append(None)

    def item_at(self, row):
        index = row.get_index() if row is not None else -1
        return self.list_items[index] if 0 <= index < len(self.list_items) else None

    def on_route_activated(self, _list, row):
        item = self.item_at(row)
        if item and item[0] in ("saved", "recent"):
            self.to_entry.set_place(item[1])
            self.tray.remember(item[1])
            self.update_star()
            self.search()

    def on_route_selected(self, _list, row):
        item = self.item_at(row)
        if not item or item[0] in ("saved", "recent"):
            return
        origin, destination, _moment = self.searched
        prefix = self.tray.settings.get("prefix") or ""
        from_name = self.from_entry.entry.get_text() or origin["name"]
        to_name = self.to_entry.entry.get_text() or destination["name"]
        if item[0] == "con":
            self.route_detail.show_connection(item[1], from_name, to_name, prefix)
        else:
            route = item[1]
            self.route_detail.show_direct(route, from_name, to_name, self.direct_start(route),
                                          map_url(route["mode"], origin, destination), item[2])

    def direct_start(self, route):
        """Losgehen fuer Rad, zu Fuss und Auto: jetzt, zur gewaehlten Zeit oder so, dass
        man zur gewaehlten Zeit ankommt."""
        if route.get("start"):                         # TomTom rechnet mit der Uhrzeit selbst
            return route["start"]
        moment = self.searched[2] if self.searched else None
        if not moment:
            return time.time()
        return moment[0] - route["duration"] if moment[1] else moment[0]

    def update_leave(self, now):
        for widget, con in self.leave_labels:
            widget.set_text(leave_text(con, now))

    # -- Gespeicherte und letzte Ziele

    def update_star(self):
        """Der Stern neben dem Ziel speichert es bzw. nimmt es wieder heraus - gefuellt und
        tuerkis, solange es gespeichert ist. Nicht bei Zuhause, das steht immer oben."""
        place, home = self.to_entry.place, self.tray.settings.get("home")
        show = place is not None and not (home and distance_m(place["latitude"], place["longitude"],
                                                              home["latitude"], home["longitude"]) < 20)
        self.star.set_visible(bool(show))
        if not show:
            return
        saved = self.tray.saved_index(place) is not None
        full = not saved and len(self.tray.settings.get("saved") or []) >= SAVED_MAX
        self.star_glyph.set("starred" if saved else "star")
        if saved:
            self.star.get_style_context().add_class("tr-active")
            self.star.set_tooltip_text("Remove from saved destinations")
        else:
            self.star.get_style_context().remove_class("tr-active")
            self.star.set_tooltip_text("You can save up to %d destinations" % SAVED_MAX if full
                                       else "Save this destination")
        self.star.set_sensitive(not full)

    def on_star(self):
        """Wieder herausgenommen kommt das Ziel zurueck zu den letzten - wie vor dem Speichern."""
        place = self.to_entry.place
        if place is None:
            return
        if self.tray.saved_index(place) is None:
            self.tray.save_place(place)
        else:
            self.tray.unsave_place(place)
            self.tray.remember(place)
        self.saved_changed()

    def saved_changed(self):
        """Gespeicherte oder letzte Ziele haben sich geaendert: Stern und Startliste neu."""
        self.update_star()
        if not self.searched:
            self.show_list()

    def save(self, place):
        self.tray.save_place(place)
        self.saved_changed()

    def unsave(self, place):
        self.tray.unsave_place(place)
        self.saved_changed()

    def move_saved(self, index, step):
        self.tray.move_saved(index, step)
        self.saved_changed()

    def forget_recent(self, place):
        self.tray.forget_recent(place)
        self.saved_changed()

    def on_edit(self):
        """"Edit" bzw. "Done": die Namen gelten schon beim Tippen."""
        self.editing = not self.editing
        self.saved_changed()

    def on_clear(self):
        self.cleared = self.tray.clear_recent()
        self.saved_changed()

    def on_undo(self):
        self.tray.restore_recent(self.cleared or [])
        self.cleared = None
        self.saved_changed()

    # -- Abfahrten

    def departures_changed(self):
        """Neue Abfahrten vom Tray (oder neue Haltestellen): die Liste neu, die Auswahl bleibt."""
        settings, cache = self.tray.settings, self.tray.cache
        prefix = settings.get("prefix") or ""
        keep = self.selected_dep
        now = time.time()
        stops = settings.get("stops") or []
        self.dep_status.set_text(updated_line(cache, self.tray.state, now).replace(" · ", SEP)
                                 if stops else "")
        # Nur neu aufbauen, wenn sich etwas geaendert hat - sonst springt die Liste. Und
        # nicht, solange der Filter einer Haltestelle offen ist: er haengt an ihrem Kopf.
        boards = [board or [] for board in ((cache or {}).get("boards") or [])[:len(stops)]]
        rules = [stop_rules(settings, stop) for stop in stops]
        shape = (bool(settings.get("home")), prefix, self.tray.busy, self.tray.state,
                 tuple((stop_key(stop), stop.get("walk"), json.dumps(rule)) for stop, rule in zip(stops, rules)),
                 tuple(tuple((d.get("jid"), d["planned"], d.get("real"), d.get("cancelled"), d.get("platform"),
                              d in reachable(board, stops[i], now))
                             for d in board if eff_time(d) >= now - 30 and not dep_hidden(d, rules[i]))
                       for i, board in enumerate(boards)))
        if shape == self.dep_shape or self.line_filter is not None:
            return
        self.dep_shape = shape
        self.clear_list(self.dep_list)
        self.dep_items = []
        if not settings.get("home") or not stops:
            self.add_dep_note("Set your home and choose stops near it - their departures show up here.")
            self.dep_detail.message("No stops chosen yet.")
            return
        select = None
        raw = (cache or {}).get("boards") or []
        for i, stop in enumerate(stops):
            self.add_dep_head(self.stop_head(stop, i, len(stops)))
            board = raw[i] if i < len(raw) else None
            if board is None:
                self.add_dep_note("Loading…" if self.tray.busy or self.tray.state == "cached" else "No departures yet.")
                continue
            ahead = [d for d in board if eff_time(d) >= now - 30 and not dep_hidden(d, rules[i])]
            if not ahead:
                self.add_dep_note(no_departures(rules[i], more=False) + ".")
            reach = reachable(board, stop, now)
            for dep in ahead:
                select = self.add_dep_row(dep, stop, dep not in reach, keep) or select
        self.dep_list.show_all()
        if select is not None:
            self.dep_list.select_row(select)
        elif keep is None:
            self.dep_detail.message("Choose a departure to see its stops on the map.")

    def stop_head(self, stop, index, count):
        """Kopf einer Haltestelle: Name, darunter der Fussweg; daneben der Trichter fuer
        ihren Filter, bei mehreren Pfeile - damit rueckt sie nach oben oder unten, hier und
        im Menue."""
        prefix = self.tray.settings.get("prefix") or ""
        head = Gtk.Box(spacing=2)
        names = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        names.pack_start(label(short_name(stop["name"], prefix), "tr-section", ellipsize=True), False, False, 0)
        if stop.get("walk") is not None:
            names.pack_start(label("%d min walk" % walk_minutes(stop["walk"]), "tr-sub", "dim-label"), False, False, 0)
        head.pack_start(names, True, True, 0)
        head.pack_start(filter_button(stop_rules(self.tray.settings, stop), prefix,
                                      lambda button: self.open_filter(button, stop)), False, False, 0)
        if count < 2:
            return head
        for key, step, tip in (("up", -1, "Move this stop up"), ("down", 1, "Move this stop down")):
            button = tool_button(key, tip, lambda s=step: self.tray.move_stop(index, s))
            button.set_sensitive(0 <= index + step < count)
            head.pack_start(button, False, False, 0)
        return head

    def open_filter(self, button, stop):
        if self.line_filter is not None:
            self.line_filter.close()
        self.line_filter = LineFilter(self.tray, stop, button, self.filter_closed)

    def filter_closed(self):
        self.line_filter = None
        if self.window is not None:
            self.departures_changed()   # jetzt mit dem neuen Filter

    def add_dep_head(self, widget):
        head = Gtk.ListBoxRow(activatable=False, selectable=False)
        styled(head, "tr-head")
        head.add(widget)
        self.dep_list.add(head)
        self.dep_items.append(None)

    def add_dep_row(self, dep, stop, unreachable, keep):
        row = Gtk.ListBoxRow()
        row.add(departure_row(dep, self.tray.settings.get("prefix") or "", unreachable))
        self.dep_list.add(row)
        self.dep_items.append((dep, stop))
        return row if keep and same_departure(dep, keep) else None

    def add_dep_note(self, text):
        row = Gtk.ListBoxRow(activatable=False, selectable=False)
        row.add(label(text, "dim-label", wrap=True))
        self.dep_list.add(row)
        self.dep_items.append(None)

    def select_departure(self, dep, stop=None):
        """Aus dem Menue: diese Abfahrt waehlen und ihren Verlauf zeigen."""
        self.show_page("departures")
        self.selected_dep = dep
        for index, item in enumerate(self.dep_items):
            if item is not None and same_departure(item[0], dep):
                self.dep_list.select_row(self.dep_list.get_row_at_index(index))
                return
        self.load_trip(dep, stop)       # nicht (mehr) in der Liste: trotzdem zeigen

    def on_dep_selected(self, _list, row):
        index = row.get_index() if row is not None else -1
        item = self.dep_items[index] if 0 <= index < len(self.dep_items) else None
        if item is None:
            return
        dep, stop = item
        if self.selected_dep is not None and same_departure(dep, self.selected_dep) \
                and self.dep_detail.showing == (dep.get("jid"), dep["line"], dep["planned"]):
            self.selected_dep = dep
            return                      # neu aufgebaute Liste, gleiche Abfahrt: Verlauf steht schon
        self.selected_dep = dep
        self.load_trip(dep, stop)

    def load_trip(self, dep, stop=None):
        self.trip_serial += 1
        self.dep_detail.message("Loading…", home=False)
        threading.Thread(target=self.fetch_trip, args=(self.trip_serial, dep, stop), daemon=True).start()

    def fetch_trip(self, serial, dep, stop=None):
        try:
            result = departure_trip(dep, stop)
        except (NoResult, Offline) as exc:
            result = exc
        except Exception as exc:  # noqa: BLE001
            log("trip details failed: %s: %s" % (type(exc).__name__, exc))
            result = ServiceError("The details did not load - try again later.")
        GLib.idle_add(self.got_trip, serial, dep, result)

    def got_trip(self, serial, dep, result):
        if serial != self.trip_serial or self.window is None:
            return GLib.SOURCE_REMOVE
        if isinstance(result, Exception):
            self.dep_detail.message(str(result) if not isinstance(result, Offline)
                                    else "No connection - try again when you are online.")
        else:
            self.dep_detail.show_trip(dep, result, self.tray.settings.get("prefix") or "")
        return GLib.SOURCE_REMOVE

    # -- Zeit, Tasten, Schliessen

    def on_tick(self):
        self.update_leave(time.time())
        if self.stack.get_visible_child_name() == "departures":
            self.departures_changed()
        return GLib.SOURCE_CONTINUE

    def on_key(self, _win, event):
        if event.keyval == Gdk.KEY_Escape:
            if self.line_filter is not None:
                self.line_filter.close()
                return True
            for entry in (self.from_entry, self.to_entry):
                if entry.popover.get_visible():
                    entry.popover.popdown()
                    return True
            if self.editing:
                self.on_edit()
                return True
            self.window.destroy()
            return True
        return False

    def on_destroy(self, _win):
        GLib.source_remove(self.tick)
        self.window = None
        self.line_filter = None
        for view in self.views:
            if view in self.tray.tiles.views:
                self.tray.tiles.views.remove(view)
        for entry in (self.from_entry, self.to_entry):
            entry.popover.destroy()
        self.tray.window_closed()


def same_departure(a, b):
    if a.get("jid") and b.get("jid"):
        return a["jid"] == b["jid"] and a["planned"] == b["planned"]
    return (a["line"], a["direction"], a["planned"]) == (b["line"], b["direction"], b["planned"])


def leave_text(con, now):
    """'leave now', 'leave in 4 min' - nur fuer die naechste Stunde."""
    minutes = int(math.floor((con["dep"] - now) / 60.0))
    if con["cancelled"] or minutes < -1 or minutes >= 60:
        return ""
    return "leave now" if minutes <= 0 else "leave in %d min" % minutes


LEGS_W = LEFT_W - 50    # so breit darf eine Zeile Etappen in der Liste werden


def connection_row(con, prefix):
    """Eine Verbindung in der Liste: Zeiten und Dauer, die Etappen als Kaestchen, wo
    man einsteigt. -> (Widget, Label fuer "leave in ...")"""
    box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=5)
    top = Gtk.Box(spacing=8)
    dep, arr = eff_time(con, "dep"), eff_time(con, "arr")
    top.pack_start(label("%s – %s" % (clock(dep, con.get("dep_tz")), clock(arr, con.get("arr_tz"))), "tr-big"),
                   False, False, 0)
    late = delay_minutes(con["arr"], con.get("arr_real"))
    if late:
        top.pack_start(label(signed(late), "tr-late", "tr-sub"), False, False, 0)
    top.pack_end(label(duration_text(arr - dep), "dim-label"), False, False, 0)
    box.pack_start(top, False, False, 0)

    items = []
    for leg in con["legs"]:
        if leg["type"] in ("walk", "bike"):             # Fussweg bzw. Rad: Symbol und Minuten
            if (leg.get("duration") or 0) < 60:
                continue
            part = Gtk.Box(spacing=2)
            part.pack_start(icon(leg["type"], 14, "dim-label"), False, False, 0)
            part.pack_start(label(str(int(round(leg["duration"] / 60.0))), "dim-label", "tr-sub"), False, False, 0)
        else:
            part = chip(leg["kind"], leg["line"], leg.get("cancelled"))
        item = Gtk.Box(spacing=5)          # "›" bleibt beim Umbruch an der Etappe danach
        if items:
            item.pack_start(label("›", "dim-label"), False, False, 0)
        item.pack_start(part, False, False, 0)
        item.show_all()
        items.append(item)
    # Viele Etappen (Umstiege mit Fusswegen): umbrechen, statt die Spalte zu verbreitern
    lines = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
    line, used = None, 0
    for item in items:
        width = item.get_preferred_width()[1]
        if line is None or used + 5 + width > LEGS_W:
            line, used = Gtk.Box(spacing=5), -5
            lines.pack_start(line, False, False, 0)
        line.pack_start(item, False, False, 0)
        used += 5 + width
    box.pack_start(lines, False, False, 0)

    info = []
    ride = next((l for l in con["legs"] if l["type"] == "ride"), None)
    if ride:
        info.append("%s %s" % (short_name(ride["from"], prefix), clock(eff_time(ride, "dep"), ride.get("dep_tz"))))
    if con["changes"]:
        info.append("%d change%s" % (con["changes"], "s" if con["changes"] > 1 else ""))
    bottom = Gtk.Box(spacing=8)
    if con["cancelled"]:
        bottom.pack_start(label("cancelled", "tr-cancel", "tr-sub"), False, False, 0)
    bottom.pack_start(label(" · ".join(info), "tr-sub", "dim-label", ellipsize=True), True, True, 0)
    leave = label("", "tr-sub", "tr-leave")
    bottom.pack_end(leave, False, False, 0)
    box.pack_start(bottom, False, False, 0)
    return box, leave


def direct_row(route, start, fastest=None):
    """Rad, zu Fuss oder Auto in der Liste: Dauer (mit Stau orange), Strecke, Ankunft,
    ueber welche Strassen. fastest: Dauer der schnellsten Route, wenn Alternativen zur
    Wahl stehen - dann steht dabei, um wie viel diese langsamer ist."""
    box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
    top = Gtk.Box(spacing=8)
    key = {"bike": "bike", "walk": "walk", "car": "car"}[route["mode"]]
    top.pack_start(icon(key, 16), False, False, 0)
    top.pack_start(label(duration_text(route["duration"]), "tr-big"), False, False, 0)
    delay = int(round((route.get("delay") or 0) / 60.0))
    if route.get("live") and route["mode"] == "car" and delay > 0:
        top.pack_start(label("+%d" % delay, "tr-late", "tr-sub"), False, False, 0)
    top.pack_end(label(distance_text(route["distance"]), "dim-label"), False, False, 0)
    box.pack_start(top, False, False, 0)
    box.pack_start(label("%s – %s" % (clock(start, route.get("tz")), clock(start + route["duration"], route.get("tz"))),
                         "tr-sub", "dim-label"),
                   False, False, 0)
    via = ["via " + (route.get("via") or route.get("summary"))] if route.get("via") or route.get("summary") else []
    slower = int(round((route["duration"] - fastest) / 60.0)) if fastest is not None else 0
    if slower > 0:
        via.append("%d min slower" % slower)
    if via:
        box.pack_start(label(" · ".join(via), "tr-sub", "dim-label", ellipsize=True), False, False, 0)
    return box


def departure_row(dep, prefix, unreachable=False):
    """Eine Abfahrt in der Liste: Uhrzeit, Linie, Richtung, Verspaetung; was man zu Fuss
    nicht mehr schafft, blass."""
    grid = Gtk.Grid(column_spacing=10)
    when_ = label(clock(eff_time(dep), dep.get("tz")), "tr-time", "dim-label" if unreachable else None)
    when_.set_size_request(40, -1)
    grid.attach(when_, 0, 0, 1, 1)
    part = chip(dep["kind"], dep["line"], dep.get("cancelled"))
    part.set_halign(Gtk.Align.START)
    grid.attach(part, 1, 0, 1, 1)
    direction = label(short_name(dep["direction"], prefix), "dim-label" if unreachable else None, ellipsize=True)
    direction.set_hexpand(True)
    grid.attach(direction, 2, 0, 1, 1)
    if dep.get("cancelled"):
        grid.attach(label("cancelled", "tr-cancel", "tr-sub"), 3, 0, 1, 1)
    else:
        late = delay_minutes(dep["planned"], dep.get("real"))
        if late:
            grid.attach(label(signed(late), "tr-late", "tr-sub"), 3, 0, 1, 1)
    if dep.get("platform") and dep["kind"] == "train":
        grid.attach(label("Platform %s%s" % (dep["platform"], " (changed)" if dep.get("platform_changed") else ""),
                          "tr-sub", "tr-late" if dep.get("platform_changed") else "dim-label"), 2, 1, 2, 1)
    if unreachable:
        grid.set_tooltip_text("Too soon to make it there on foot")
    return grid


def platform_text(leg, which):
    """'Platform 3' (Abfahrt bzw. Ankunft einer Fahrt), mit '(changed)' bei Gleiswechsel."""
    if leg.get("type") != "ride" or not leg.get(which + "_platform"):
        return None
    return "Platform %s%s" % (leg[which + "_platform"], " (changed)" if leg.get(which + "_platform_changed") else "")


def merged_walk(walks):
    """Mehrere Fusswege hintereinander als einer (Weg zum Bahnhof und Umstieg darin)."""
    meters = sum(w.get("distance") or 0 for w in walks)
    return dict(walks[0], to=walks[-1]["to"], to_coord=walks[-1].get("to_coord"), arr=walks[-1]["arr"],
                arr_real=walks[-1].get("arr_real"), distance=meters or None,
                duration=sum(w.get("duration") or 0 for w in walks))


class Detail:
    """Rechts: die schwebende Karte mit Kopf und Verlauf als Zeitleiste - und was sie
    zeigt, auch auf der Landkarte darunter."""

    def __init__(self, view, owner):
        self.view = view
        self.owner = owner
        self.widget = Gtk.ScrolledWindow(hscrollbar_policy=Gtk.PolicyType.NEVER,
                                         vscrollbar_policy=Gtk.PolicyType.AUTOMATIC)
        self.box = styled(Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=12), "tr-detail")
        self.widget.add(self.box)
        self.showing = None

    def clear(self):
        for child in self.box.get_children():
            child.destroy()
        self.showing = None

    def message(self, text, home=True):
        """Ein Hinweis statt eines Verlaufs; die Karte zeigt dann Zuhause und Haltestellen."""
        self.clear()
        note = label(text, "dim-label", xalign=0.5, wrap=True)
        note.set_justify(Gtk.Justification.CENTER)
        note.set_valign(Gtk.Align.CENTER)
        note.set_vexpand(True)
        note.set_max_width_chars(34)
        self.box.pack_start(note, True, True, 0)
        self.box.show_all()
        if home:
            self.view.set_content(*home_map(self.owner.tray.settings))

    def head(self, title, sub=None, key=None, chip_=None, markup=None):
        row = Gtk.Box(spacing=10)
        if chip_ is not None:
            chip_.set_valign(Gtk.Align.START)
            row.pack_start(chip_, False, False, 0)
        elif key:
            row.pack_start(icon(key, 22), False, False, 0)
        text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
        text.pack_start(label(title, "tr-title", wrap=True), False, False, 0)
        if sub:
            text.pack_start(label(sub, "dim-label", wrap=True), False, False, 0)
        if markup:
            extra = label("", "tr-sub", wrap=True)
            extra.set_markup(markup)
            text.pack_start(extra, False, False, 0)
        row.pack_start(text, True, True, 0)
        self.box.pack_start(row, False, False, 0)

    def show_connection(self, con, from_name, to_name, prefix):
        """Eine Verbindung Schritt fuer Schritt: Haltestellen mit Zeiten und Steig,
        dazwischen Fahrten (mit Betreiber und aufklappbaren Halten) und Fusswege."""
        self.clear()
        dep, arr = eff_time(con, "dep"), eff_time(con, "arr")
        changes = con["changes"]
        legs = con["legs"]
        start_tz, end_tz = con.get("dep_tz"), con.get("arr_tz")
        sub = "%s – %s · %s" % (clock(dep, start_tz), clock(arr, end_tz),
                                "direct" if not changes else "%d change%s" % (changes, "s" if changes > 1 else ""))
        self.head(duration_text(arr - dep), sub, "tram", markup=source_markup("Route by", con.get("planner")))
        line = Timeline()
        last_ride = None                # Index der letzten Fahrt davor
        i = 0
        while i < len(legs):
            leg = legs[i]
            if leg["type"] == "bike":           # mit dem Rad (zur Haltestelle, Rad + Oeffis)
                if i == 0:
                    line.node(from_name, leg["dep"], None, None, None, "solo", tz=start_tz)
                elif last_ride == i - 1:
                    came = legs[last_ride]
                    line.node(short_name(leg["from"], prefix), came["arr"], came.get("arr_real"),
                              platform_text(came, "arr"), "ride", "solo", tz=came.get("arr_tz"))
                else:
                    line.node(short_name(leg["from"], prefix), leg["dep"], None, None, "walk", "solo",
                              tz=leg.get("dep_tz"))
                after = legs[i + 1] if i + 1 < len(legs) else None
                line.leg("solo", bike_content(leg, after is not None and after["type"] == "ride"))
                i += 1
                continue
            if leg["type"] == "walk":
                # aufeinanderfolgende Fusswege (Weg und Umstieg im Bahnhof) zusammen
                j = i
                while j + 1 < len(legs) and legs[j + 1]["type"] == "walk":
                    j += 1
                walk = leg if j == i else merged_walk(legs[i:j + 1])
                after = legs[j + 1] if j + 1 < len(legs) else None
                if last_ride is not None and after is not None:
                    # Umstieg mit Fussweg: Ankunft, dann Weg und Wartezeit bis zur naechsten Fahrt
                    came = legs[last_ride]
                    line.node(short_name(leg["from"], prefix), came["arr"], came.get("arr_real"),
                              platform_text(came, "arr"), "ride", "walk", tz=came.get("arr_tz"))
                    line.leg("walk", change_content(walk, came, after))
                else:                       # Fussweg am Anfang oder am Ende
                    if last_ride is None and i == 0:
                        line.node(from_name, walk["dep"], walk.get("dep_real"), None, None, "walk", tz=start_tz)
                    elif last_ride is None:     # nach dem Rad zu Fuss weiter
                        line.node(short_name(leg["from"], prefix), walk["dep"], None, None, "solo", "walk",
                                  tz=leg.get("dep_tz"))
                    else:
                        came = legs[last_ride]
                        line.node(short_name(leg["from"], prefix), came["arr"], came.get("arr_real"),
                                  platform_text(came, "arr"), "ride", "walk", tz=came.get("arr_tz"))
                    line.leg("walk", walk_content(walk))
                i = j + 1
                continue
            prev = legs[i - 1] if i else None
            before = None if prev is None else RAIL_STYLES[prev["type"]]
            name = from_name if i == 0 else short_name(leg["from"], prefix)
            change = arrival = None
            if prev is not None and prev["type"] == "ride":     # Umstieg am selben Steig
                change = change_content(None, prev, leg)
                arrival = (prev["arr"], prev.get("arr_real"))
            line.node(name, leg["dep"], leg.get("dep_real"), platform_text(leg, "dep"), before, "ride",
                      cancelled=leg.get("cancelled"), arrival=arrival, change=change, tz=leg.get("dep_tz"))
            line.leg("ride", ride_content(leg, prefix))
            last_ride = i
            i += 1
        last = legs[-1]
        if last["type"] == "ride":
            line.node(to_name, last["arr"], last.get("arr_real"), platform_text(last, "arr"), "ride", None, end=True,
                      tz=end_tz)
        else:
            line.node(to_name, last["arr"], last.get("arr_real"), None, RAIL_STYLES[last["type"]], None, end=True,
                      tz=end_tz)
        self.box.pack_start(line.grid, False, False, 0)
        self.box.show_all()
        self.view.set_content(*connection_map(con))

    def show_direct(self, route, from_name, to_name, start, url, others=()):
        """Rad, zu Fuss oder Auto: Dauer mit Verkehr, Meldungen, die Strassen der Reihe
        nach. others: die anderen Autorouten - auf der Karte grau dahinter."""
        self.clear()
        mode = route["mode"]
        title = "%s · %s" % (duration_text(route["duration"]), distance_text(route["distance"]))
        sub = "%s – %s" % (clock(start, route.get("tz")), clock(start + route["duration"], route.get("tz")))
        if route.get("via") or route.get("summary"):
            sub += " · via " + (route.get("via") or route["summary"])
        notes = []
        if route.get("live"):
            delay = int(round((route.get("delay") or 0) / 60.0))
            if mode == "car":
                notes.append('<span foreground="%s">+%d min traffic</span>' % (self.owner.warning_hex(), delay)
                             if delay > 0 else "No delays right now")
            notes.append("Live traffic: TomTom")
        else:
            notes.append("Without live traffic" + (" and parking" if mode == "car" else "") + " · OpenStreetMap")
        if route.get("warning"):
            notes.append('<span foreground="%s">%s</span>' % (self.owner.warning_hex(),
                                                              GLib.markup_escape_text(route["warning"])))
        self.head(title, sub, mode, markup="\n".join(notes))
        jams = [j for j in route.get("traffic") or [] if j.get("delay") or j.get("category") != "OTHER"]
        if jams:
            box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
            for jam in jams[:6]:
                row = Gtk.Box(spacing=8)
                row.pack_start(icon("warning", 14, "tr-late"), False, False, 0)
                meters = sum(distance_m(a[1], a[0], b[1], b[0]) for a, b in zip(jam["coords"], jam["coords"][1:]))
                text = TRAFFIC_WORDS.get(jam.get("category"), "Slow traffic")
                if jam.get("delay"):
                    text += " · +%s" % duration_text(jam["delay"])
                if meters:
                    text += " · " + distance_text(meters)
                row.pack_start(label(text, "tr-sub"), False, False, 0)
                box.pack_start(row, False, False, 0)
            self.box.pack_start(box, False, False, 0)
        style = "walk" if mode == "walk" else "solo"
        line = Timeline()
        line.node(from_name, start, None, None, None, style, tz=route.get("tz"))
        for step in route["steps"]:
            box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=1)
            box.pack_start(label(step["name"], "tr-name", ellipsize=True), False, False, 0)
            turn = step["turn"] if len(step["turn"]) < 60 else step["turn"][:57] + "…"
            box.pack_start(label("%s · %s" % (turn, distance_text(step["distance"])), "tr-sub", "dim-label", wrap=True),
                           False, False, 0)
            line.leg(style, box)
        line.node(to_name, start + route["duration"], None, None, style, None, end=True, tz=route.get("tz"))
        self.box.pack_start(line.grid, False, False, 0)
        button = Gtk.Button(label="Open in OpenStreetMap")
        button.set_halign(Gtk.Align.START)
        button.connect("clicked", lambda _b: open_uri(url))
        self.box.pack_start(button, False, False, 0)
        self.box.show_all()
        self.view.set_content(*direct_map(route, others))

    def show_trip(self, dep, trip, prefix):
        """Der Verlauf einer Abfahrt: ab der eigenen Haltestelle alle Halte bis zum Ziel."""
        self.clear()
        stops = trip["stops"]
        start = next((i for i, s in enumerate(stops) if s["name"] == dep.get("at") and s["dep"] == dep["planned"]),
                     next((i for i, s in enumerate(stops) if s["dep"] is not None
                           and abs(s["dep"] - dep["planned"]) <= 60), 0))
        rest = stops[start:]
        direction = short_name(trip["direction"] or dep["direction"], prefix)
        late = delay_minutes(dep["planned"], dep.get("real"))
        sub = "from %s at %s" % (short_name(dep.get("at") or rest[0]["name"], prefix),
                                 clock(eff_time(dep), dep.get("tz")))
        sub += " · cancelled" if dep.get("cancelled") else " · %s late" % duration_text(late * 60) if late > 0 \
            else " · on time" if dep.get("real") is not None else ""
        if dep.get("platform"):
            sub += " · Platform %s" % dep["platform"]
        self.head("→ " + direction, sub, chip_=chip(dep["kind"], dep["line"], dep.get("cancelled")),
                  markup=source_markup("Departure from", dep.get("source")))
        line = Timeline()
        for i, stop in enumerate(rest):
            first, final = i == 0, i == len(rest) - 1
            planned = stop["dep"] if stop["dep"] is not None and not final else stop["arr"]
            real = stop["dep_real"] if stop["dep"] is not None and not final else stop["arr_real"]
            if first and dep.get("source") in EFA_SOURCES:      # Abfahrt vom Betreiber, nicht von der ÖBB
                planned, real = dep["planned"], dep.get("real")
            line.node(short_name(stop["name"], prefix), planned, real, None, None if first else "ride",
                      None if final else "ride", end=final, minor=not (first or final),
                      cancelled=stop.get("cancelled"), tz=stop.get("tz") or dep.get("tz"))
        self.box.pack_start(line.grid, False, False, 0)
        self.box.show_all()
        self.showing = (dep.get("jid"), dep["line"], dep["planned"])
        self.view.set_content(*trip_map(trip, start))


def home_map(settings):
    """Karte ohne Auswahl: Zuhause und die gewaehlten Haltestellen."""
    markers = []
    home = settings.get("home")
    if home:
        markers.append({"kind": "home", "coord": (home["longitude"], home["latitude"])})
    for stop in settings.get("stops") or []:
        if stop.get("latitude"):
            markers.append({"kind": "sign", "coord": (stop["longitude"], stop["latitude"])})
    return [], markers


def connection_map(con):
    legs, markers = [], []
    for leg in con["legs"]:
        coords = leg.get("path") or [c for c in (leg.get("from_coord"), leg.get("to_coord")) if c]
        legs.append({"style": {"ride": "ride", "bike": "cycle"}.get(leg["type"], "walk"), "coords": coords})
        if leg["type"] == "ride":
            markers += [{"kind": "minor", "coord": s["coord"]} for s in leg.get("stops") or [] if s.get("coord")]
            markers += [{"kind": "stop", "coord": c} for c in (leg.get("from_coord"), leg.get("to_coord")) if c]
    first = con["legs"][0].get("from_coord") or (legs[0]["coords"][0] if legs and legs[0]["coords"] else None)
    last = con["legs"][-1].get("to_coord") or (legs[-1]["coords"][-1] if legs and legs[-1]["coords"] else None)
    if first:
        markers.append({"kind": "start", "coord": first})
    if last:
        markers.append({"kind": "end", "coord": last})
    return legs, markers


def direct_map(route, others=()):
    """Eine Route auf der Karte; die anderen Autorouten grau darunter."""
    style = {"walk": "walk", "bike": "bike", "car": "car"}[route["mode"]]
    coords = route.get("coords") or []
    markers = []
    if coords:
        markers = [{"kind": "start", "coord": coords[0]}, {"kind": "end", "coord": coords[-1]}]
    legs = [{"style": "alt", "coords": other.get("coords") or []} for other in others]
    return legs + [{"style": style, "coords": coords, "traffic": route.get("traffic") or []}], markers


def trip_map(trip, start):
    stops = trip["stops"]
    markers = []
    for i, stop in enumerate(stops):
        if not stop.get("coord") or i < start:
            continue
        kind = "stop" if i == start else "end" if i == len(stops) - 1 else "minor"
        markers.append({"kind": kind, "coord": stop["coord"]})
    path = trip.get("path") or []
    return [{"style": "ride", "coords": path}], markers


def open_uri(url):
    try:
        Gio.AppInfo.launch_default_for_uri(url, None)
    except GLib.Error as exc:
        log("could not open %s: %s" % (url, exc.message))


# ------------------------------------------------------------------ Filter: Linien und Richtungen

FILTER_W = 330          # Breite des Filter-Popovers
FILTER_LIST_H = 440     # Hoehe seiner Liste hoechstens
FILTER_CHROME = 230     # Titel, Hinweis, Fuss und Abstand zum Fensterrand


def cached_board(cache, key):
    """Die Abfahrten der Haltestelle key im letzten Stand (oder None)."""
    stops, boards = (cache or {}).get("stops") or [], (cache or {}).get("boards") or []
    return boards[stops.index(key)] if key in stops and stops.index(key) < len(boards) else None


def filter_button(rules, prefix, callback):
    """Der Trichter neben einer Haltestelle oeffnet ihren Filter - tuerkis, solange er
    etwas weglaesst."""
    button = styled(Gtk.Button(), "tr-order", "tr-active" if rules else None)
    button.add(icon("filter", 14))
    button.set_tooltip_text("Hidden: %s" % filter_text(rules, prefix) if rules else "Choose lines and directions")
    button.set_valign(Gtk.Align.CENTER)
    button.connect("clicked", callback)
    return button


class LineFilter:
    """Popover am Trichter einer Haltestelle: welche Linien und Richtungen Menue und
    Abfahrten zeigen. Abgehakt heisst weggelassen; was neu dazukommt, steht da, bis man
    es abhakt. Zuerst die Linien aus dem letzten Stand, dann alle der naechsten Stunden
    (Tray.survey). Ein Klick auf die Linie schaltet alle ihre Richtungen.
    Popover ragen unter GTK3 nicht ueber ihr Fenster hinaus: side ist die Seite mit Platz
    (in "Home & stops" links ueber der Liste, unter Departures rechts ueber der Karte),
    die Hoehe richtet sich nach dem Fenster."""

    def __init__(self, tray, stop, anchor, closed=None, side="right"):
        self.tray, self.stop, self.key, self.closed = tray, stop, stop_key(stop), closed
        self.deps = list(cached_board(tray.cache, self.key) or [])
        self.rows = []                  # (Linie, Kaestchen, Knopf, [(Haken, Richtung, Text)])
        self.quiet = False              # True, waehrend sync die Haken setzt
        self.popover = styled(Gtk.Popover(relative_to=anchor), "tr-popover")
        self.popover.set_position(Gtk.PositionType.LEFT if side == "left" else Gtk.PositionType.RIGHT)
        self.popover.connect("closed", self.on_closed)
        self.popover.connect("destroy", self.on_destroyed)
        # Breite fest: umbrechende Labels melden sonst die ganze Zeile als Wunschbreite, das
        # Popover wuerde breiter als das Fenster und links abgeschnitten
        box = styled(Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8), "tr-filter")
        box.set_size_request(FILTER_W, -1)
        prefix = tray.settings.get("prefix") or ""
        title = label(short_name(stop["name"], prefix), "tr-section", ellipsize=True)
        hint = label("Untick what the menu and Departures should leave out. New lines and destinations "
                     "show up until you untick them.", "tr-sub", "dim-label", wrap=True)
        for widget, chars in ((title, 30), (hint, 44)):
            widget.set_max_width_chars(chars)
            box.pack_start(widget, False, False, 0)
        scroller = Gtk.ScrolledWindow(hscrollbar_policy=Gtk.PolicyType.NEVER,
                                      vscrollbar_policy=Gtk.PolicyType.AUTOMATIC)
        scroller.set_propagate_natural_height(True)
        room = anchor.get_toplevel().get_allocated_height() - FILTER_CHROME
        scroller.set_max_content_height(max(160, min(FILTER_LIST_H, room)))
        self.grid = Gtk.Grid(column_spacing=12, row_spacing=8)
        scroller.add(self.grid)
        box.pack_start(scroller, True, True, 0)
        foot = Gtk.Box(spacing=8)
        self.note = label("Looking for all lines here…", "tr-sub", "dim-label", wrap=True)
        self.note.set_max_width_chars(30)
        foot.pack_start(self.note, True, True, 0)
        self.reset = Gtk.Button(label="Show all")
        self.reset.set_valign(Gtk.Align.CENTER)
        self.reset.connect("clicked", self.on_reset)
        foot.pack_end(self.reset, False, False, 0)
        box.pack_start(foot, False, False, 0)
        self.popover.add(box)
        box.show_all()
        self.fill()
        tray.survey(stop, self.surveyed)
        self.popover.popup()

    def rules(self):
        return stop_rules(self.tray.settings, self.stop)

    def fill(self):
        for child in self.grid.get_children():
            child.destroy()
        self.rows = []
        prefix = self.tray.settings.get("prefix") or ""
        groups = line_groups(self.deps, self.rules())
        if not groups:
            self.grid.attach(label("No lines known here yet.", "dim-label"), 0, 0, 2, 1)
        for n, group in enumerate(groups):
            box = chip(group["kind"], group["line"])
            button = styled(Gtk.Button(), "tr-chipbtn")
            button.add(box)
            button.set_valign(Gtk.Align.START)
            button.set_halign(Gtk.Align.START)
            button.connect("clicked", self.on_line, group)
            self.grid.attach(button, 0, n, 1, 1)
            column = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
            checks = []
            # Linie ganz aus und gerade ohne Fahrt: ein Haken fuer alle Richtungen
            for direction in group["dirs"] or [None]:
                text = label(" · ".join(short_name(t, prefix) for t in direction["towards"]) if direction
                             else "all directions", wrap=True)
                text.set_max_width_chars(30)
                check = Gtk.CheckButton()
                check.add(text)
                check.connect("toggled", self.on_direction, group, direction)
                column.pack_start(check, False, False, 0)
                checks.append((check, direction, text))
            self.grid.attach(column, 1, n, 1, 1)
            self.rows.append((group, box, button, checks))
        self.grid.show_all()
        self.sync()

    def sync(self):
        """Haken, graue Kaestchen und "Show all" nach den Regeln - ohne die Liste neu zu bauen."""
        rules = self.rules()
        self.reset.set_sensitive(bool(rules))
        for group, box, button, checks in self.rows:
            off = line_hidden(rules, group["line"]) or bool(group["dirs"]) and all(
                direction_hidden(rules, group, d) for d in group["dirs"])
            ctx = box.get_style_context()
            (ctx.add_class if off else ctx.remove_class)("tr-cancelled")
            button.set_tooltip_text("%s all of line %s" % ("Show" if off else "Hide", group["line"]))
            for check, direction, text in checks:
                active = not off if direction is None else not direction_hidden(rules, group, direction)
                if check.get_active() != active:
                    self.quiet = True
                    check.set_active(active)
                    self.quiet = False
                ctx = text.get_style_context()
                (ctx.remove_class if active else ctx.add_class)("dim-label")

    def on_direction(self, check, group, direction):
        if self.quiet:
            return
        if direction is None:
            rules = toggle_line(self.rules(), group, check.get_active())
        else:
            rules = toggle_direction(self.rules(), group, direction, check.get_active())
        self.tray.set_filter(self.key, rules)
        self.sync()

    def on_line(self, _button, group):
        rules = self.rules()
        off = line_hidden(rules, group["line"]) or bool(group["dirs"]) and all(
            direction_hidden(rules, group, d) for d in group["dirs"])
        self.tray.set_filter(self.key, toggle_line(rules, group, off))
        self.sync()

    def on_reset(self, _button):
        self.tray.set_filter(self.key, [])
        self.sync()

    def surveyed(self, deps, note):
        if self.popover is None:
            return
        if deps is not None:
            self.deps = list(deps) + self.deps
        self.note.set_text(note or "Lines running in the next %d hours." % (SURVEY_MIN // 60))
        self.fill()

    def close(self):
        if self.popover is not None:
            self.popover.popdown()

    def on_closed(self, popover):
        if self.popover is None:
            return
        self.popover = None
        GLib.idle_add(popover.destroy)
        if self.closed:
            self.closed()

    def on_destroyed(self, _popover):
        if self.popover is not None:    # mit dem Fenster zu
            self.popover = None
            if self.closed:
                self.closed()


# ------------------------------------------------------------------ Zuhause und Haltestellen

class HomeWindow:
    """Zuhause suchen und waehlen, dann die Haltestellen in der Naehe an- und abwaehlen.
    Die gewaehlten stehen oben in der Reihenfolge des Menues, mit Pfeilen zum Umsortieren
    und dem Trichter fuer ihren Filter. Jede Aenderung gilt sofort."""

    def __init__(self, tray):
        prepare_ui()
        self.tray = tray
        self.serial = 0
        self.places = []
        self.nearby = []                # Haltestellen in der Naehe, nach Gehzeit
        self.checks = {}                # Zeile -> (CheckButton, Haltestelle), in Listenreihenfolge
        self.line_filter = None         # offenes Filter-Popover
        self.stale = False              # Liste neu bauen, sobald der Filter zu ist

        win = self.window = Gtk.Window(title="Transit Home")
        win.set_default_size(480, 780)
        win.set_position(Gtk.WindowPosition.CENTER)
        win.connect("destroy", self.on_destroy)
        win.connect("key-press-event", self.on_key)
        header_bar(win, "Home & stops")

        body = styled(Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=10), "tr-body")
        body.pack_start(label("Home", "tr-section"), False, False, 0)
        self.home_row = Gtk.Box(spacing=10)
        self.home_row.pack_start(icon("home", 20, "dim-label"), False, False, 0)
        names = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=1)
        self.home_name = label("", "tr-name", ellipsize=True)
        self.home_sub = label("", "tr-sub", "dim-label", ellipsize=True)
        names.pack_start(self.home_name, False, False, 0)
        names.pack_start(self.home_sub, False, False, 0)
        self.home_row.pack_start(names, True, True, 0)
        body.pack_start(self.home_row, False, False, 0)

        self.entry = Gtk.SearchEntry(placeholder_text="Search for your address or a stop")
        self.entry.connect("search-changed", self.on_search)
        self.entry.connect("activate", self.on_enter)
        self.entry.connect("key-press-event", self.on_entry_key)
        body.pack_start(self.entry, False, False, 0)
        self.results = styled(Gtk.ListBox(selection_mode=Gtk.SelectionMode.NONE), "tr-list", "tr-card")
        self.results.connect("row-activated", self.on_result)
        body.pack_start(self.results, False, False, 0)
        self.status = label("", "tr-sub", "dim-label", wrap=True)
        body.pack_start(self.status, False, False, 0)

        body.pack_start(label("Stops nearby", "tr-section"), False, False, 0)
        body.pack_start(label("The menu shows departures from the stops you tick (up to %d), in the order "
                              "listed here: the arrows move a stop up or down, the funnel picks its lines and "
                              "directions. Walking time counts: what you cannot reach on foot is left out."
                              % MAX_STOPS, "tr-sub", "dim-label", wrap=True), False, False, 0)
        self.abroad = label("", "tr-sub", "dim-label", wrap=True)
        self.abroad.set_markup('Outside Austria, stops and timetables come from <a href="%s">Transitous</a> - '
                               'the open data of the operators, with live times where they share them.'
                               % TRANSITOUS_SOURCES)
        body.pack_start(self.abroad, False, False, 0)
        scroller = Gtk.ScrolledWindow(hscrollbar_policy=Gtk.PolicyType.NEVER,
                                      vscrollbar_policy=Gtk.PolicyType.AUTOMATIC, vexpand=True)
        self.stop_list = styled(Gtk.ListBox(selection_mode=Gtk.SelectionMode.NONE), "tr-list")
        self.stop_list.connect("row-activated", self.on_stop_row)
        scroller.add(self.stop_list)
        frame = styled(Gtk.Box(), "tr-card")
        frame.pack_start(scroller, True, True, 0)
        body.pack_start(frame, True, True, 0)

        # Live-Verkehr: TomTom-Schluessel
        body.pack_start(label("Live traffic", "tr-section"), False, False, 0)
        body.pack_start(label("Car routes with current traffic and closures, bike and walking routes around "
                              "closures: TomTom, with a free key (no credit card, 2,500 routes a day). Without a "
                              "key, routes come from OpenStreetMap without traffic.", "tr-sub", "dim-label",
                              wrap=True), False, False, 0)
        keyrow = Gtk.Box(spacing=8)
        self.key_entry = Gtk.Entry(placeholder_text="Paste your TomTom API key", hexpand=True)
        # Verdeckt wie ein Passwort (Kopieren geht dann nicht), das Auge zeigt ihn
        self.key_entry.set_input_purpose(Gtk.InputPurpose.PASSWORD)
        self.key_entry.set_property("caps-lock-warning", False)
        self.key_entry.set_text(self.tray.settings.get("tomtom_key") or "")
        self.show_key(False)
        self.key_entry.connect("icon-press", lambda entry, _pos, _event: self.show_key(not entry.get_visibility()))
        self.key_entry.connect("activate", self.on_check_key)
        keyrow.pack_start(self.key_entry, True, True, 0)
        self.key_button = Gtk.Button(label="Save")
        self.key_button.connect("clicked", self.on_check_key)
        keyrow.pack_start(self.key_button, False, False, 0)
        body.pack_start(keyrow, False, False, 0)
        keyfoot = Gtk.Box(spacing=8)
        self.key_status = label("", "tr-sub", "dim-label", wrap=True)
        keyfoot.pack_start(self.key_status, True, True, 0)
        get_key = Gtk.LinkButton.new_with_label(TOMTOM_SIGNUP, "Get a free key")
        keyfoot.pack_end(get_key, False, False, 0)
        body.pack_start(keyfoot, False, False, 0)
        self.show_key_state()
        win.add(body)
        win.show_all()
        self.results.set_visible(False)
        self.show_home()
        if self.tray.settings.get("home"):
            self.load_stops()
        else:
            self.status.set_text("Type your address, for example “Landstraße 1, Linz”.")
            self.stop_note("Choose your home first.")
        self.entry.grab_focus()

    # -- Zuhause

    def show_home(self):
        home = self.tray.settings.get("home")
        self.home_name.set_text(home["name"] if home else "Not set yet")
        self.home_sub.set_text(home.get("sub") or "" if home else "")
        self.home_sub.set_visible(bool(home and home.get("sub")))
        self.abroad.set_visible(bool(home) and not in_austria(home["latitude"], home["longitude"]))

    def on_search(self, entry):
        text = entry.get_text().strip()
        self.serial += 1
        if len(text) < 2:
            self.show_places([])
            self.status.set_text("")
            return
        self.status.set_text("Searching…")
        threading.Thread(target=self.search, args=(text, self.serial), daemon=True).start()

    def search(self, text, serial):
        try:
            places, note = search_places(text, self.tray.settings.get("home")), None
            # Zuhause ist meist eine Adresse: Adressen vor Haltestellen vor Geschaeften
            places.sort(key=lambda p: {"A": 0, "S": 1}.get(p["type"], 2))
        except Offline:
            places, note = [], "No connection - try again when you are online."
        except Exception as exc:  # noqa: BLE001
            log("place search failed: %s: %s" % (type(exc).__name__, exc))
            places, note = [], "The search did not work - try again later."
        GLib.idle_add(self.found, serial, places, note)

    def found(self, serial, places, note):
        if self.window is None or serial != self.serial:
            return GLib.SOURCE_REMOVE   # Fenster zu oder schon weiter getippt
        self.show_places(places)
        self.status.set_text(note or ("" if places else "Nothing found."))
        return GLib.SOURCE_REMOVE

    def show_places(self, places):
        for child in self.results.get_children():
            child.destroy()
        self.places = places[:8]
        for place in self.places:
            box = Gtk.Box(spacing=10)
            box.pack_start(icon("stop" if place["type"] == "S" else "pin", 16, "dim-label"), False, False, 0)
            text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=1)
            text.pack_start(label(place["name"], "tr-name", ellipsize=True), False, False, 0)
            if place.get("sub"):
                text.pack_start(label(place["sub"], "tr-sub", "dim-label", ellipsize=True), False, False, 0)
            box.pack_start(text, True, True, 0)
            self.results.add(box)
        self.results.show_all()
        self.results.set_visible(bool(self.places))

    def on_result(self, _list, row):
        self.choose(self.places[row.get_index()])

    def on_enter(self, _entry):
        if self.places:
            self.choose(self.places[0])

    def on_entry_key(self, _entry, event):
        row = self.results.get_row_at_index(0)
        if event.keyval in (Gdk.KEY_Down, Gdk.KEY_KP_Down) and row is not None and self.results.get_visible():
            row.grab_focus()
            return True
        return False

    def choose(self, place):
        """Neues Zuhause: speichern, dann die Haltestellen in der Naehe mit Vorauswahl."""
        settings = dict(self.tray.settings, home=place, stops=[], prefix="")
        self.tray.settings_changed(settings)
        self.entry.set_text("")
        self.show_places([])
        self.status.set_text("")
        self.show_home()
        self.load_stops(preselect=True)

    # -- Haltestellen

    def stop_note(self, text):
        for child in self.stop_list.get_children():
            child.destroy()
        row = Gtk.ListBoxRow(activatable=False, selectable=False)
        row.add(label(text, "dim-label", wrap=True))
        self.stop_list.add(row)
        self.stop_list.show_all()

    def load_stops(self, preselect=False):
        self.serial += 1
        self.stop_note("Looking for stops nearby…")
        home = dict(self.tray.settings["home"])
        threading.Thread(target=self.fetch_stops, args=(home, self.serial, preselect), daemon=True).start()

    def fetch_stops(self, home, serial, preselect):
        try:
            stops, note = nearby_stops(home), None
        except Offline:
            stops, note = None, "No connection - the stops show up when you are online. Open this window again then."
        except NoResult:
            stops, note = [], None
        except Exception as exc:  # noqa: BLE001
            log("stop search failed: %s: %s" % (type(exc).__name__, exc))
            stops, note = None, "The stops did not load - try again later."
        GLib.idle_add(self.got_stops, serial, stops, note, preselect)

    def got_stops(self, serial, stops, note, preselect):
        if self.window is None or serial != self.serial:
            return GLib.SOURCE_REMOVE
        settings = self.tray.settings
        if stops is None:
            self.nearby = list(settings.get("stops") or [])
            self.show_stops()
            if not self.nearby:
                self.stop_note(note)
            else:
                self.status.set_text(note)
            return GLib.SOURCE_REMOVE
        prefix = town_prefix([s["name"] for s in stops])
        chosen = default_stops(stops) if preselect else None
        # Gewaehlte, die die Suche nicht mehr liefert, bleiben oben stehen
        known = {stop_key(s) for s in stops}
        extra = [s for s in settings.get("stops") or [] if stop_key(s) not in known]
        self.nearby = extra + stops
        if chosen is not None or prefix != settings.get("prefix"):
            new = dict(settings, prefix=prefix)
            if chosen is not None:
                new["stops"] = [dict(s) for s in chosen]
            self.tray.settings_changed(new)
        self.show_stops()
        if not self.nearby:
            self.stop_note("No stops within %.0f km of your home." % (NEAR_M / 1000.0))
        return GLib.SOURCE_REMOVE

    def show_stops(self):
        """Oben die gewaehlten in der Reihenfolge des Menues, darunter die anderen nach Gehzeit."""
        if self.line_filter is not None:
            self.stale = True           # das offene Popover haengt an einer Zeile
            return
        self.stale = False
        for child in self.stop_list.get_children():
            child.destroy()
        self.checks = {}
        chosen = list(self.tray.settings.get("stops") or [])
        keys = {stop_key(s) for s in chosen}
        others = [s for s in self.nearby if stop_key(s) not in keys]
        if chosen and others:
            self.stop_head("In the menu")
        for index, stop in enumerate(chosen):
            self.stop_row(stop, index, len(chosen))
        if chosen and others:
            self.stop_head("More stops nearby")
        for stop in others:
            self.stop_row(stop)
        self.stop_list.show_all()
        self.limit_checks()

    def stop_head(self, text):
        row = styled(Gtk.ListBoxRow(activatable=False, selectable=False), "tr-head")
        row.add(label(text, "tr-sub", "dim-label"))
        self.stop_list.add(row)

    def stop_row(self, stop, index=None, count=0):
        """Eine Haltestelle; index: ihr Platz im Menue (gewaehlt), sonst None."""
        settings = self.tray.settings
        prefix = settings.get("prefix") or ""
        box = Gtk.Box(spacing=10)
        check = Gtk.CheckButton()
        check.set_active(index is not None)
        check.set_valign(Gtk.Align.CENTER)
        box.pack_start(check, False, False, 0)
        text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=1)
        text.pack_start(label(short_name(stop["name"], prefix), "tr-name", ellipsize=True), False, False, 0)
        parts = []
        if stop.get("walk") is not None:
            parts.append("%d min walk" % walk_minutes(stop["walk"]))
        if stop.get("distance") is not None:
            parts.append(distance_text(stop["distance"]))
        text.pack_start(label(" · ".join(parts), "tr-sub", "dim-label"), False, False, 0)
        # Woher die Abfahrten kommen: gelernt (gewaehlt), sonst wer die Haltestelle kennt
        sources = stop.get("serve") or [k for k in ("wl", "linzag", "oebb", "vor", "ooevv")
                                        if k in (stop.get("ids") or {})]
        badges = Gtk.Box(spacing=4)
        for source in sources:
            badges.pack_start(styled(label(SOURCE_NAMES[source]), "tr-badge", "dim-label"), False, False, 0)
        text.pack_start(badges, False, False, 2)
        rules = stop_rules(settings, stop) if index is not None else []
        if rules:
            hidden = label("Hidden: " + filter_text(rules, prefix), "tr-sub", "dim-label", ellipsize=True)
            hidden.set_tooltip_text(filter_text(rules, prefix))
            text.pack_start(hidden, False, False, 0)
        box.pack_start(text, True, True, 0)
        # Trichter und Pfeile; bei den anderen bleibt der Platz frei, die Symbole stehen buendig
        tools = Gtk.Box(spacing=2)
        tools.set_size_request(3 * 26 + 2 * 2, -1)
        if index is not None:
            tools.pack_start(filter_button(rules, prefix, lambda button: self.open_filter(button, stop)),
                             False, False, 0)
            for key, step, tip in (("up", -1, "Move this stop up"), ("down", 1, "Move this stop down")):
                if count < 2:
                    break
                button = tool_button(key, tip, lambda s=step: self.tray.move_stop(index, s))
                button.set_sensitive(0 <= index + step < count)
                tools.pack_start(button, False, False, 0)
        box.pack_end(tools, False, False, 0)
        kinds = Gtk.Box(spacing=4)
        for kind in stop.get("kinds") or []:
            image = icon(kind, 16, "dim-label")
            image.set_tooltip_text(KIND_NAMES[kind])
            kinds.pack_start(image, False, False, 0)
        box.pack_end(kinds, False, False, 0)
        row = Gtk.ListBoxRow()
        row.add(box)
        self.stop_list.add(row)
        self.checks[row] = (check, stop)
        check.connect("toggled", self.on_toggle)

    def on_stop_row(self, _list, row):
        check = (self.checks.get(row) or (None, None))[0]
        if check is not None and check.get_sensitive():
            check.set_active(not check.get_active())

    def on_toggle(self, _check):
        """Die gewaehlten bleiben in ihrer Reihenfolge, neu abgehakte kommen ans Ende. Danach
        steht die Liste neu: abgehakte oben, die anderen darunter."""
        ticked = [stop for check, stop in self.checks.values() if check.get_active()]
        keys = {stop_key(stop) for stop in ticked}
        stops = [dict(s) for s in self.tray.settings.get("stops") or [] if stop_key(s) in keys]
        known = {stop_key(s) for s in stops}
        stops = (stops + [dict(stop) for stop in ticked if stop_key(stop) not in known])[:MAX_STOPS]
        self.tray.settings_changed(dict(self.tray.settings, stops=stops))
        self.limit_checks()
        GLib.idle_add(self.restack)

    def restack(self):
        if self.window is not None and self.checks:
            self.show_stops()
        return GLib.SOURCE_REMOVE

    def stops_changed(self):
        """Reihenfolge, Filter oder die gelernten Betreiber haben sich geaendert."""
        if self.window is not None and (self.checks or self.stale):
            self.show_stops()

    def open_filter(self, button, stop):
        if self.line_filter is not None:
            self.line_filter.close()
        self.line_filter = LineFilter(self.tray, stop, button, self.filter_closed, side="left")

    def filter_closed(self):
        self.line_filter = None
        if self.window is not None and self.stale:
            self.show_stops()

    # -- TomTom

    def show_key(self, visible):
        """Den Schluessel zeigen oder verdecken - das Auge rechts im Feld."""
        where = Gtk.EntryIconPosition.SECONDARY
        self.key_entry.set_visibility(visible)
        self.key_entry.set_icon_from_icon_name(where, "view-conceal-symbolic" if visible else "view-reveal-symbolic")
        self.key_entry.set_icon_tooltip_text(where, "Hide the key" if visible else "Show the key")

    def show_key_state(self):
        key = self.tray.settings.get("tomtom_key")
        self.key_status.set_text("Live traffic is on." if key else "No key yet - routes without traffic.")

    def on_check_key(self, _widget):
        key = self.key_entry.get_text().strip()
        if not key:
            self.tray.settings_changed(dict(self.tray.settings, tomtom_key=None))
            self.show_key_state()
            return
        self.key_button.set_sensitive(False)
        self.key_status.set_text("Checking the key with TomTom…")
        threading.Thread(target=self.check_key, args=(key,), daemon=True).start()

    def check_key(self, key):
        problem = check_tomtom_key(key)
        GLib.idle_add(self.key_checked, key, problem)

    def key_checked(self, key, problem):
        if self.window is None:
            return GLib.SOURCE_REMOVE
        self.key_button.set_sensitive(True)
        if problem:
            self.key_status.set_text(problem)
        else:
            self.tray.settings_changed(dict(self.tray.settings, tomtom_key=key))
            self.key_status.set_text("Key works - live traffic is on.")
            self.show_key(False)
        return GLib.SOURCE_REMOVE

    def limit_checks(self):
        """Hoechstens MAX_STOPS - sonst wird das Menue zu lang."""
        full = sum(1 for check, _s in self.checks.values() if check.get_active()) >= MAX_STOPS
        for check, _stop in self.checks.values():
            check.set_sensitive(check.get_active() or not full)

    def on_key(self, _win, event):
        if event.keyval == Gdk.KEY_Escape:
            if self.line_filter is not None:
                self.line_filter.close()
            else:
                self.window.destroy()
            return True
        return False

    def on_destroy(self, _win):
        self.window = None
        self.line_filter = None
        self.tray.home_closed()




# ------------------------------------------------------------------ Befehle

def load_gtk():
    """GTK und AppIndicator laden - nur fuer den Tray-Modus noetig."""
    global AppIndicator, Gdk, GdkPixbuf, Gio, GLib, Gtk, Pango, PangoCairo
    import warnings
    # Gtk.ImageMenuItem ist veraltet, aber der einzige Weg zu Bildern im Menue (Tray.image_item).
    warnings.filterwarnings("ignore", message=r"Gtk\.ImageMenuItem\.", category=DeprecationWarning)
    import gi
    gi.require_version("Gtk", "3.0")
    gi.require_version("Gdk", "3.0")
    gi.require_version("GdkPixbuf", "2.0")
    gi.require_version("AyatanaAppIndicator3", "0.1")
    gi.require_version("Pango", "1.0")
    gi.require_version("PangoCairo", "1.0")
    from gi.repository import AyatanaAppIndicator3 as AppIndicator, Gdk, GdkPixbuf, Gio, GLib, Gtk, Pango, PangoCairo
    # Wird die App-ID unter Wayland. GTK naehme sonst den Skriptnamen "transit-tray.py" -
    # dazu gibt es keinen Starter, und das Dock zeigte beim Fenster kein Symbol.
    GLib.set_prgname(APP_ICON)


def single_instance():
    """Offene Lock-Datei oder None, wenn schon eine Instanz laeuft. Darin steht
    unsere PID - so findet --route das laufende Widget."""
    os.makedirs(RUNTIME_DIR, exist_ok=True)
    fh = open(LOCK_FILE, "a+")              # nicht "w": das loeschte die PID der laufenden Instanz
    try:
        fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        fh.close()
        return None
    fh.seek(0)
    fh.truncate()
    fh.write("%d\n" % os.getpid())
    fh.flush()
    return fh


def ask_running_to_open(window):
    """Dem laufenden Widget sagen, dass es ein Fenster oeffnet: welches und das
    Aktivierungs-Token des Starters stehen in ACTIVATE_FILE, dann kommt SIGUSR1."""
    try:
        with open(LOCK_FILE) as fh:
            pid = int(fh.read().split()[0])
    except (OSError, ValueError, IndexError):
        return False
    token = os.environ.get("XDG_ACTIVATION_TOKEN") or os.environ.get("DESKTOP_STARTUP_ID")
    write_json(ACTIVATE_FILE, {"window": window, "token": token})
    try:
        os.kill(pid, signal.SIGUSR1)
    except OSError:
        return False
    return True


def take_activation():
    try:
        with open(ACTIVATE_FILE, encoding="utf-8") as fh:
            data = json.load(fh)
        os.remove(ACTIVATE_FILE)
    except (OSError, ValueError):
        return "route", None
    if not isinstance(data, dict):
        return "route", None
    return (data.get("window") if data.get("window") in ("route", "home") else "route"), data.get("token") or None


def cmd_once():
    settings = load_settings()
    if not settings.get("home"):
        print("No home set yet - open the widget and choose “Home & stops…”.")
        return EXIT_CODES["nohome"]
    now = time.time()
    changed = False
    for stop in settings["stops"]:              # wie im Tray: wer faehrt hier (einmal die Woche)
        if not stop.get("serve") or now - (stop.get("learned") or 0) >= LEARN_AGE:
            try:
                stop["serve"], sure = learn_serves(stop, now)
                stop["learned"] = now if sure else now - LEARN_AGE + 3600
                changed = True
            except (Offline, ServiceError, NoResult) as exc:
                log("could not learn the operators at %s (%s)" % (stop["name"], exc))
    if changed:
        save_settings(settings)
    old = load_cache(settings)
    cache, state, detail = fetch_state(settings, now, old)
    if detail:
        log(detail)
    if cache is not None:
        write_json(CACHE_FILE, cache)
    else:
        cache = old
    for line in terminal_lines(settings, cache, state, time.time()):
        print(line)
    return EXIT_CODES[state]


def run_tray(window=None):
    """window: "route" oder "home" - dieses Fenster gleich oeffnen."""
    lock = single_instance()            # bleibt offen, solange der Prozess laeuft
    if lock is None:
        if window and ask_running_to_open(window):
            return 0
        print("transit-tray: already running")
        return 0
    # Bis unten die eigentlichen Handler stehen: SIGUSR1 (--route, --home) und SIGHUP
    # (tray-wait --guard) ignorieren - sonst beendeten sie das Widget im Start.
    for sig in (signal.SIGUSR1, signal.SIGHUP):
        signal.signal(sig, signal.SIG_IGN)
    load_gtk()
    ensure_app_icons()
    tray = Tray()
    if window == "home":
        tray.open_home()                # das Token aus der Umgebung nutzt GTK selbst
    elif window == "route":
        tray.open_window("route")

    def show(*_args):
        name, token = take_activation()
        if name == "home":
            tray.open_home(token)
        else:
            tray.open_window("route", token=token)
        return GLib.SOURCE_CONTINUE

    def stop(*_args):
        Gtk.main_quit()
        return GLib.SOURCE_REMOVE

    def restart_self(*_args):
        # SIGHUP von tray-wait --guard: neu starten. Mit neuer Busverbindung meldet
        # sich das Symbol neu an und steht wieder hinten in der Leiste.
        os.execv(sys.executable, [sys.executable] + [a for a in sys.argv if a not in ("--route", "--home")])

    for sig in (signal.SIGINT, signal.SIGTERM):
        GLib.unix_signal_add(GLib.PRIORITY_DEFAULT, sig, stop)
    GLib.unix_signal_add(GLib.PRIORITY_DEFAULT, signal.SIGUSR1, show)
    GLib.unix_signal_add(GLib.PRIORITY_DEFAULT, signal.SIGHUP, restart_self)
    Gtk.main()
    return 0


def main():
    ap = argparse.ArgumentParser(description="Public transport departures and route planner in the COSMIC status area")
    ap.add_argument("--once", action="store_true",
                    help="fetch once, print the menu lines and exit "
                         "(exit code 0 ok, 2 no home set, 3 offline, 4 error)")
    ap.add_argument("--route", action="store_true",
                    help="open the route planner (starts the widget if it is not running)")
    ap.add_argument("--home", action="store_true",
                    help="choose home and stops (starts the widget if it is not running)")
    args = ap.parse_args()
    if args.once:
        return cmd_once()
    return run_tray("home" if args.home else "route" if args.route else None)


if __name__ == "__main__":
    sys.exit(main())
