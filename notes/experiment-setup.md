# Experimente: Aufbau und Stand

Stand: 22.11.2026. Stufe 1 ist gebaut und mit synthetischen Daten getestet (siehe „Stand der Umsetzung“). Die übrigen Abschnitte sind der ursprüngliche Vorschlag; wo er überholt ist, steht es im nächsten Abschnitt.

## Stand der Umsetzung

Entschieden (Antworten vom 22.11.2026): Im Labor steht ein Linux-Rechner mit NVIDIA-GPU, den Stefan bedient. Der Mac hat 16 GB Arbeitsspeicher und etwa 50 GB freien Plattenplatz. Stufe 1 wird gebaut.

Gebaut und getestet (Linux x86-64, ohne Docker):

- `lean/ContractMonitors/Perception.lean`: Contracts für System, Detektion, Tracking und Prädiktion als Instanzen der Muster, 31 Monitore, alle Schranken als Parameter.
- `lean/Main.lean`: Programm `monitor`, liest eine Tick-Datei und schreibt je Tick die Verdikte aller Monitore.
- `experiments/tools/ticks.py`, `sim.py`, `evaluate.py` und `experiments/run.py`: Tick-Format, synthetische Kette mit Fehlerinjektion, Kennzahlen, Kampagne.
- Synthetische Kampagne (5 Seeds, 19 Kombinationen aus Kanal und Fehlerklasse): kein Alarm in den 5 fehlerfreien Läufen, 95 von 95 Fehlern erkannt, Zuordnung in allen 95 Läufen richtig. Das zeigt nur, dass die Werkzeuge zusammenspielen. Kette und Contracts stammen aus derselben Hand, die Zahlen sind kein Ergebnis für das Paper.

Bewiesen (22.11.2026, `lean/ContractMonitors/Temporal.lean` und `Perception.lean`):

- `Perception.refines`: Die Komposition der Contracts von Detektion, Tracking und Prädiktion verfeinert den System-Contract, für alle Werte der Schranken. Damit ist die Voraussetzung der Sätze zum verfeinerungserhaltenden Monitoring für genau die Contracts bewiesen, die das Programm `monitor` ausführt.
- `Perception.system_guarantee_of_silent_monitors`: Trace-Version des Satzes, instanziiert für die Perzeptionskette.
- `Perception.extendable`: Systemannahme und Komponentengarantien sind zusammen erweiterbar. Zeuge ist eine „sichere Beobachtung“ (auf jedem Kanal kommt eine geänderte Nachricht an, ohne Inhalt, den eine Schranke ablehnen könnte); nach ihr gilt jede Klausel unabhängig von der Vorgeschichte. Damit gilt auch die Präfix-Version (`Perception.system_guarantee_on_prefix`) ohne unbewiesene Voraussetzung.
- Zwei Kettenregeln für die Muster: Antwortfenster addieren sich (`respondsWithin_chain`); eine Komponente mit Antwortfenster k reicht Lebendigkeit mit um k vergrößertem Fenster weiter (`aliveWithin_chain`).
- Stefan hat die synthetische Kampagne im Docker-Container auf dem M1 ausgeführt und dieselbe Tabelle erhalten. Dockerfile und Stufe 1 laufen damit auf arm64.

Geschrieben, aber ungetestet:

- `experiments/tools/extract.py` (rosbag2 nach Tick-Datei): ohne Aufzeichnung geschrieben. Topic-Namen, Feldnamen der Autoware-Nachrichten und das Registrieren der Nachrichtendefinitionen sind an einem echten Bag zu prüfen.

Abweichungen vom Vorschlag unten:

1. **Fehlerinjektion in aufgezeichnete Bags reicht nicht.** Ein Fehler, der nachträglich in ein aufgezeichnetes Topic eingesetzt wird, wirkt nicht auf die nachgelagerten Komponenten: Deren aufgezeichnete Ausgaben stammen aus dem fehlerfreien Lauf. Die Garantie-Monitore stromabwärts sehen dann Ausgaben, die zu den gestörten Eingaben nicht passen, und die Zuordnung (RQ3) wird verfälscht. Folge: Für RQ2 und RQ3 muss der Fehler vor dem (erneuten) Lauf der nachgelagerten Komponenten injiziert werden. Tracking und Prädiktion brauchen keine GPU, die Detektion schon. Die gestörten Läufe entstehen deshalb auf dem Laborrechner, einmal je Fehlerfall; der Mac wertet die so erzeugten Bags aus. Rein offline gültig bleiben nur Fehler auf dem letzten Kanal der Kette. Die Aussage „Schritt B enthält alle Messungen“ im Abschnitt „Kernidee“ gilt daher nur für Auswertung und Monitorlauf, nicht für die Injektion.
2. **Probelauf 2a besser im Labor.** Mit 16 GB Arbeitsspeicher und etwa 50 GB Platz ist das Autoware-Image auf dem Mac knapp. Der Probelauf mit dem Beispiel-Bag findet auf dem Laborrechner statt; der Mac bleibt für Stufe 1.
3. **Format.** Tick-Dateien sind einfache Textzeilen (`name=wert`), nicht JSON Lines. Das spart einen JSON-Parser in Lean. Das Lean-Programm heißt `lean/Main.lean`, die Injektion steckt in `sim.py` statt in einem eigenen `inject.py`.

Offen:

- Fehlerinjektion für die echte Kette: ein kleiner ROS-2-Knoten, der ein Topic umleitet und stört, auf dem Laborrechner.
- Schranken in `experiments/configs/params.default` an die gemessenen Topic-Raten anpassen.

## Ausgangslage

Drei Tatsachen bestimmen den Aufbau:

1. **Autoware läuft als Container auf arm64.** Die Autoware Foundation veröffentlicht Multi-Arch-Images (amd64, arm64), darunter ein Laufzeit-Image ohne GPU.
2. **Der gelernte Detektor läuft dort nicht.** Ohne CUDA steht für die LiDAR-Objekterkennung nur der regelbasierte Modus `clustering` zur Verfügung. Alle Detektoren mit neuronalem Netz (CenterPoint und andere) brauchen TensorRT und damit eine NVIDIA-GPU.
3. **Docker auf dem Mac erreicht keine GPU.** Container laufen in einer Linux-VM ohne Zugriff auf die Apple-GPU; CUDA gibt es dort ohnehin nicht.

Folge: Die KI-Komponente selbst lässt sich auf dem M1 nicht ausführen. Alles andere schon.

## Kernidee: Perzeption und Monitoring entkoppeln

Die Monitore beobachten nur Topics. Für RQ2 und RQ3 werden Fehler auf Topic-Ebene injiziert. Beides braucht keine laufende Perzeption, sondern nur deren aufgezeichnete Ein- und Ausgaben.

Deshalb zwei getrennte Schritte:

- **Schritt A, einmalig, auf einer GPU-Maschine:** Autoware-Perzeption auf den Benchmark-Daten laufen lassen und Ein- und Ausgangs-Topics als rosbag2 aufzeichnen.
- **Schritt B, beliebig oft, auf dem Mac:** Die aufgezeichneten Bags auswerten, Fehler injizieren, Monitore ausführen, Kennzahlen berechnen.

Schritt B enthält alle Messungen des Papers und ist vollständig reproduzierbar, weil er keine Echtzeit und kein ROS zur Laufzeit braucht.

## Stufe 1: Offline-Auswertung auf dem Mac (Kern der Experimente)

Ein schlanker Container (arm64) mit Lean und Python. Kein ROS, kein Autoware.

Ablauf:

1. `extract`: liest ein rosbag2 mit der reinen Python-Bibliothek `rosbags` (keine ROS-Installation nötig) und erzeugt je Tick eine Belegung der beobachteten Kanäle als JSON-Zeile. Die Tickdauer ist ein Parameter.
2. `inject`: wendet eine Fehlerklasse aus dem Fehlermodell auf die Tick-Folge an (Ort: Eingang oder Ausgang einer Komponente; Zeitpunkt; Dauer) und protokolliert die Injektion als Referenz.
3. `monitor`: das aus Lean kompilierte Programm liest die Tick-Folge und gibt je Tick die Verdikte aller Annahme- und Garantie-Monitore aus.
4. `evaluate`: vergleicht Verdikte mit dem Injektionsprotokoll und berechnet Erkennungsrate, Erkennungsverzögerung, Fehlalarme und Zuordnung.

Was dafür noch zu bauen ist:

- In Lean: ein ausführbares Programm (`lake exe monitor`), der Beobachtungstyp für die Perzeptionskette und die konkreten Contracts als Instanzen der Muster.
- In Python: `extract`, `inject`, `evaluate`.

Skizze des Containers (ungetestet):

```dockerfile
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y curl git python3 python3-pip python3-venv && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"
RUN python3 -m venv /opt/venv && /opt/venv/bin/pip install rosbags
ENV PATH="/opt/venv/bin:${PATH}"
WORKDIR /work
```

Aufruf (ungetestet):

```bash
docker build -t cm-monitor -f experiments/docker/monitor.Dockerfile .
docker run --rm -v "$PWD":/work -v "$HOME/cm-data":/data cm-monitor \
  bash -c "cd lean && lake build monitor && cd .. && python3 experiments/run.py --bags /data/bags --out /data/results"
```

Lean lädt beim ersten `lake build` die im Projekt festgelegte Version nach. Da Lean auch macOS auf Apple Silicon unterstützt, geht Stufe 1 alternativ ganz ohne Docker; der Container hat den Vorteil, dass er später das Artefakt für die Einreichung ist.

## Stufe 2: Bags erzeugen

Drei Wege, mit zunehmender Aussagekraft:

| Weg | Wo | Detektor | Eignung |
|---|---|---|---|
| 2a | Mac, Autoware-arm64-Container ohne GPU | `clustering` (regelbasiert) | Probelauf und Minimaltest der Kette; keine gelernte Komponente, daher nicht für die Ergebnisse des Papers |
| 2b | Linux-Rechner mit NVIDIA-GPU (Labor), Autoware-CUDA-Container | CenterPoint | **empfohlen für das Paper** |
| 2c | Cloud-Instanz mit GPU | CenterPoint | Ausweichlösung, falls kein Laborrechner verfügbar ist |

Für 2a auf dem Mac (ungetestet, Tag und Startargumente an die aktuelle Autoware-Dokumentation anpassen):

```bash
docker pull ghcr.io/autowarefoundation/autoware:universe-humble
# im Container: logging_simulator mit perception:=true und lidar_detection_model:=clustering starten,
# parallel ros2 bag play <eingabe> und ros2 bag record <perzeptions-topics>
```

Hinweise zu 2a: Das Image ist groß (zweistelliger GB-Bereich), Docker Desktop sollte reichlich Arbeitsspeicher zugeteilt bekommen, und ob die Perzeption auf dem M1 in Echtzeit mithält, ist offen. Für Bags ist Echtzeit nicht nötig: Die Wiedergabe lässt sich verlangsamen (`ros2 bag play --rate 0.2`).

Eingabedaten: zunächst der Autoware-Beispiel-Bag (läuft ohne Anpassung), dann nuScenes mini (etwa 4 GB, zehn Szenen) nach Konvertierung in rosbag2. Die Anpassung an das nuScenes-Sensorsetup ist das bekannte Risiko mit Rückfall-Termin Mitte Januar 2027.

## Stufe 3: Online-Betrieb mit ROS 2 (optional)

Ein zweiter Container mit ROS 2 Humble (arm64) und einem kleinen Adapter-Knoten in Python: Er tastet die Topics je Tick ab, reicht die Belegung an den Lean-Monitor weiter und veröffentlicht die Verdikte. Der Bag wird mit `ros2 bag play` abgespielt.

Zweck: nicht die Messung, sondern die Validierung des Adapters. Für denselben Bag müssen Online- und Offline-Verdikte übereinstimmen; Abweichungen zeigen Effekte von Abtastung und Nachrichtenverlust. Das beantwortet den offenen Punkt „wie wurde der Adapter validiert“ in den Threats to Validity.

Anbindung des Lean-Monitors: zunächst als eigener Prozess, der Belegungen zeilenweise liest und Verdikte zeilenweise schreibt. Das vermeidet eine C-Schnittstelle zwischen Lean und ROS und genügt für die Validierung.

## Reihenfolge und Aufwand

| Schritt | Inhalt | Wo | Abhängigkeit |
|---|---|---|---|
| 1 | Lean-Programm `monitor`, `extract`/`inject`/`evaluate`, Test mit synthetischen Daten | Mac oder hier im Repository | keine |
| 2 | Probelauf 2a mit dem Autoware-Beispiel-Bag, Topic-Raten ablesen, Tickdauer festlegen | Mac | Schritt 1 |
| 3 | Contracts für Detektion, Tracking, Prädiktion mit konkreten Schranken instanziieren | Repository | Schritt 2 |
| 4 | Bags mit CenterPoint erzeugen (2b) | GPU-Rechner | Zugang zu einem GPU-Rechner |
| 5 | Messkampagne RQ2/RQ3 | Mac | Schritte 3 und 4 |
| 6 | Online-Validierung des Adapters (Stufe 3) | Mac | Schritt 1 |

Schritt 1 lässt sich sofort beginnen und vollständig ohne Autoware testen.

## Vorgeschlagene Ablage im Repository

```
experiments/
  docker/monitor.Dockerfile      Stufe 1
  docker/ros.Dockerfile          Stufe 3
  tools/extract.py               rosbag2 -> Tick-Belegungen (JSON Lines)
  tools/inject.py                Fehlerinjektion mit Protokoll
  tools/evaluate.py              Kennzahlen für RQ2 und RQ3
  run.py                         Kampagne über alle Bags und Fehlerklassen
  configs/                       Topics, Tickdauer, Schranken, Fehlerparameter
lean/Monitor.lean                ausführbares Programm
```

Daten und Ergebnisse liegen außerhalb des Repositorys (`~/cm-data`), weil nuScenes nicht weitergegeben werden darf.

## Offene Fragen

- Steht ein Linux-Rechner mit NVIDIA-GPU für Weg 2b zur Verfügung, und wer bedient ihn?
- Wie viel Arbeitsspeicher und freien Plattenplatz hat der Mac? Das entscheidet, ob Weg 2a praktikabel ist.
- Soll Stufe 1 im Container oder direkt unter macOS laufen?
