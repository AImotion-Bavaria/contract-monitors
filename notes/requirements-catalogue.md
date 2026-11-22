# Anforderungskatalog für RQ1 (Ausdrucksstärke) – erster Durchgang

Stand: 22.11.2026. Entwurf, noch nicht gegen alle Quellen geprüft.

## Zweck

RQ1 fragt, welcher Anteil realistischer Sicherheitsanforderungen an eine Perzeptionskette im monitorbaren Contract-Fragment ausdrückbar ist. Dieser Katalog sammelt Kandidaten aus drei Quellen und ordnet jeder Anforderung ein Schema und eine Einstufung zu.

## Quellen

- **T25** – Monitoring-Aspekte der Taxonomie aus Okumus et al., ECSA 2025 (Tabelle 1 des Papers).
- **AW** – Autoware: Perzeptions-Design und -Schnittstelle (docs.autoware.org), `topic_state_monitor`, `autoware_pipeline_latency_monitor`.
- **SUR** – Survey „Safety Monitoring of Machine Learning Perception Functions“ (arXiv:2412.06869), Abschnitt 5.

Spalte „Beleg“: **b** = in der Quelle so benannt; **a** = aus der Quelle abgeleitet, Formulierung von uns, vor Verwendung im Paper zu belegen.

## Einstufung

- **ja** – als Instanz eines Schemas aus `Patterns.lean` ausdrückbar; der Korrektheitssatz deckt den Monitor ab.
- **Signal** – nur als Atom über einem außerhalb des Monitors berechneten Signal; die Berechnung des Signals liegt außerhalb des Beweises.
- **teilweise** – eine abgeschwächte oder eingeschränkte Fassung ist ausdrückbar.
- **nein** – nicht ausdrückbar oder an der Schnittstelle nicht beobachtbar.

## Katalog

| ID | Anforderung | Quelle | Beleg | Schema | Einstufung | Begründung |
|---|---|---|---|---|---|---|
| R01 | Antwortzeit zwischen Eingabe und Ausgabe höchstens τ | T25 | b | Response | ja | |
| R02 | Nachrichtenrate eines Kanals entspricht f | T25 | b | Liveliness + Mindestabstand | ja | untere Schranke über Fenster, obere über Mindestabstand |
| R03 | Wert liegt im Bereich [l, u] | T25 | b | Invariant | ja | |
| R04 | Wert erfüllt Schwellwertbedingung | T25 | b | Invariant | ja | |
| R05 | Zeitliche Konsistenz: Abweichung über Δt höchstens ε | T25 | b | Bounded step | teilweise | für Δt = 1 Tick ja; für Δt > 1 fehlt der Vergleich mit dem Wert vor k Ticks |
| R06 | Zeitliche Konsistenz: Abweichung vom gleitenden Mittel höchstens ε | T25 | b | Invariant | Signal | Aggregat über Fenster |
| R07 | Datenquellen beschreiben dasselbe Phänomen (Korrelation, zeitversetzt) | T25 | b | Invariant | Signal | Korrelation ist ein Aggregat |
| R08 | Ressourcenverbrauch unter Schwelle | T25 | b | Invariant | ja | sofern der Verbrauch als Kanal vorliegt |
| R09 | Liveliness: Nachrichten im Abstand Δt ± ε | T25 | b | Liveliness + Mindestabstand | ja | |
| R10 | Topic wird nach dem Start empfangen | AW | b | Liveliness | ja | `topic_state_monitor`: NotReceived |
| R11 | Topic-Rate fällt nicht unter Warn- bzw. Fehlerschwelle | AW | b | Liveliness | teilweise | „mindestens eine Nachricht je Fenster“ ja; „mindestens n Nachrichten je Fenster“ braucht Zählen |
| R12 | Kein Ausbleiben eines Topics länger als T | AW | b | Liveliness | ja | `topic_state_monitor`: Timeout |
| R13 | Latenz der Verarbeitungskette unter Schwelle | AW | b | Response | ja | Ende-zu-Ende-Response zwischen Ein- und Ausgangskanal |
| R14 | Diagnosestatus eines Knotens ist OK | AW | a | Invariant | ja | Diagnose als Kanal |
| R15 | Zu jeder Punktwolke wird ein Detektionsergebnis veröffentlicht | AW | a | Response | ja | |
| R16 | Getrackte Objekte gehen auf Detektionen zurück | AW | a | Provenance | teilweise | auf Nachrichtenebene ja; je Objekt-ID nein (Quantor über Objekte) |
| R17 | Zu getrackten Objekten liegen Prädiktionen vor | AW | a | Response | ja | auf Nachrichtenebene |
| R18 | Objektpositionen liegen im Erfassungsbereich | AW | a | Invariant | ja | Atom quantifiziert innerhalb einer Nachricht |
| R19 | Geschwindigkeit und Abmessungen je Klasse plausibel | AW | a | Invariant | ja | |
| R20 | Zeitstempel sind monoton, Daten nicht veraltet | AW | a | Bounded step / Invariant | ja | |
| R21 | Eingangsstatistik im Normalbereich (Rauschen, Beleuchtung, Tropfen) | SUR | b | Invariant | Signal | Bildverarbeitung außerhalb des Monitors |
| R22 | Rekonstruktionsfehler der Eingabe unter Schwelle | SUR | b | Invariant | Signal | eigenes Modell berechnet den Score |
| R23 | Vorhergesagte Ausfallwahrscheinlichkeit unter Schwelle (Introspektion) | SUR | b | Invariant | Signal | |
| R24 | Unsicherheit der Vorhersage unter Schwelle | SUR | b | Invariant / Bounded duration | Signal | sofern die Komponente die Unsicherheit nicht selbst ausgibt |
| R25 | Konfidenz über Schwelle bzw. nicht anhaltend darunter | SUR | b | Invariant / Bounded duration | ja | Konfidenz ist Teil der Ausgabe |
| R26 | Aktivierungsmuster interner Schichten bekannt | SUR | b | – | nein | an der Schnittstelle nicht beobachtbar |
| R27 | Kohärenz zwischen Schichten | SUR | b | – | nein | an der Schnittstelle nicht beobachtbar |
| R28 | Kein Flackern von Detektionen über Frames | SUR | b | Bounded step | teilweise | über die Objektanzahl ja; je Objekt nein |
| R29 | Größe und Lage von Bounding Boxes plausibel | SUR | b | Invariant | ja | |
| R30 | Ausgabe verträglich mit Verkehrsregel-Logik | SUR | b | Invariant | teilweise | nur soweit die Regel über eine Belegung entscheidbar ist |
| R31 | Übereinstimmung mehrerer Modelle (Ensemble) | SUR | b | Invariant | teilweise | ja, wenn beide Ausgaben Kanäle sind; sonst Signal |
| R32 | Stabilität der Ausgabe unter Eingabestörung | SUR | b | – | nein | erfordert erneute Ausführung des Modells |
| R33 | Konsistenz mit unabhängigem Sensor | SUR | b | Invariant | Signal | geometrischer Abgleich außerhalb des Monitors |
| R34 | Jedes Objekt wird irgendwann getrackt | SUR | a | Response | teilweise | unbeschränkt nein (Liveness); mit Frist ja |
| R35 | Enthaltungsrate der Komponente beschränkt | SUR | a | Bounded duration | teilweise | „nicht länger als k Ticks in Folge“ ja; Rate über Fenster braucht Zählen |

## Zwischenstand

| Einstufung | Anzahl | Anteil |
|---|---|---|
| ja | 17 | 49 % |
| teilweise | 8 | 23 % |
| Signal | 7 | 20 % |
| nein | 3 | 9 % |
| Summe | 35 | |

Die Zahlen sind vorläufig: Die Auswahl stammt aus einem ersten Durchgang, 9 der 35 Einträge sind abgeleitet statt belegt, und die Einstufung ist noch nicht durch Formalisierung jedes Eintrags in Lean abgesichert.

## Beobachtungen

Drei Lücken kehren wieder und erklären fast alle Einträge „teilweise“:

1. **Zählen im Fenster** (R11, R35): „mindestens n Ereignisse in den letzten k Ticks“. Ein Operator mit beschränktem Zähler wäre eine kleine Spracherweiterung.
2. **Vergleich über mehr als einen Tick** (R05): Das zweistellige Atom vergleicht nur benachbarte Beobachtungen. Ein Puffer der letzten k Beobachtungen bliebe speicherbeschränkt.
3. **Aussagen je Objekt** (R16, R28, R34): Eigenschaften einzelner Objekt-IDs über die Zeit brauchen Quantoren über Daten. Das liegt grundsätzlich außerhalb einer aussagenlogischen Sprache und wäre als Grenze zu benennen.

Die Einträge „Signal“ betreffen durchweg Größen, die ein eigenes Modell oder eine Signalverarbeitung berechnet. Die Einträge „nein“ betreffen Interna der Komponente oder verlangen deren erneute Ausführung.

## Offene Arbeiten

- Abgeleitete Einträge (Beleg **a**) an der Autoware-Dokumentation belegen oder streichen.
- Jeden Eintrag „ja“ und „teilweise“ als Formel in Lean aufschreiben; die Einstufung gilt erst dann als gesichert.
- Prüfen, ob ISO/PAS 8800 und weitere Quellen Anforderungen liefern, die hier fehlen.
- Entscheiden, ob die Sprache um Zählen im Fenster und einen k-Schritt-Vergleich erweitert wird.
