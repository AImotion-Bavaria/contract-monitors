# Experimente lokal auf einem Mac mit M1: Vorschlag

Stand: 22.11.2026. Vorschlag, noch nichts davon ist ausprobiert. Die Docker-Skizzen unten sind ungetestet.

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
