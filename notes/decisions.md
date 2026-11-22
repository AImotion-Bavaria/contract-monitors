# ECSA 2027 – Entscheidungen und Stand

Stand: 22.11.2026

## Rahmen

- Venue: ECSA 2027, Research Track, Porto, 27.09.–01.10.2027
- Abstract (Pflicht): 12.03.2027 · Paper: 19.03.2027 · Notification: 28.04.2027 (jeweils AoE)
- Format: Springer LNCS, 16 Seiten + 2 Seiten (Data Availability, Danksagung, Referenzen); Limit laut Call noch vorläufig
- Begutachtung doppelt anonym; Abschnitt „Data Availability“ ist Pflicht
- Autor: zunächst allein
- Sprache/Stil: britisches Englisch, „we“, strukturiertes Abstract, FOCUS-Notation, Stil früherer Publikationen

## Thema

Eigenständiges Paper. Das ECSA-2025-Paper (Okumus et al.) wird als vorhandene Vorarbeit zitiert, nicht fortgeschrieben.

Zuschnitt: verfeinerungserhaltendes Monitoring als Kern, Contracts für KI-Komponenten als Evaluation, Beweisassistent als Mittel.

Kernaussage (Entwurf): Monitore für KI-Komponenten lassen sich aus hierarchisch verfeinerten A/G-Contracts so synthetisieren, dass sie der Architektur folgen; maschinell bewiesen wird, dass lokale Monitore zusammen den übergeordneten Contract absichern.

Titel (Arbeitsfassung): Verified Compositional Runtime Monitoring for AI-Enabled Software Architectures

## Beiträge

1. Contract-Rahmen über getakteten Strömen: Verfeinerung, Komposition, Präfix-Semantik
2. Kompositionale Synthese entlang der Verfeinerungshierarchie mit mechanisierten Sätzen
3. Contract-Muster für Perzeption (ODD-Annahmen, Plausibilität, zeitliche Konsistenz, Konfidenz)
4. Evaluation an der Autoware-Perzeptionskette mit nuScenes-Daten und Fehlerinjektion

## Forschungsfragen

- RQ1 Ausdrucksstärke: Welcher Anteil realistischer Sicherheitsanforderungen an eine Perzeptionskette ist im monitorbaren Fragment ausdrückbar?
- RQ2 Erkennung: Erkennen Komponenten-Monitore Verletzungen des System-Contracts, mit welcher Verzögerung und Fehlalarmrate?
- RQ3 Lokalisierung: Ordnen getrennte Annahme- und Garantie-Monitore eine Verletzung korrekt zu?

Gestrichen: Laufzeit-Overhead als Forschungsfrage.
Modelltreue (Taktung, Nachrichtenverlust, Gleitkomma) wird als Threat to Validity behandelt.
Mechanisierungsaufwand wird im Diskussionsteil berichtet.

## Sätze und Stand im Lean-Projekt (`lean/`)

Das Projekt baut mit Lean 4.35.0 ohne Mathlib und enthält kein `sorry`.

| Satz | Inhalt | Lean | Stand |
|---|---|---|---|
| Verfeinerung | Präordnung, Korrektheit | `Refines.refl`, `Refines.trans`, `Sat.of_refines` | bewiesen |
| Komposition | unabhängige Implementierbarkeit, Monotonie | `Sat.comp`, `comp_mono` | bewiesen |
| T1 | Monitor-Korrektheit der Synthese | `synthMonitor_correct` | bewiesen |
| T1b | beschränkter Speicher (Zähler ≤ Fensterlänge + 1, Puffer ≤ k) | `Machine.ctr_le`, `lag_buffer_le`, `count_buffer_le` | bewiesen |
| T2 | zentral = verteilt | `verdict_prod`, `Correct.prod` | bewiesen |
| T3 | Verfeinerungserhalt, Trace-Version | `system_guarantee_of_no_component_alarm` | bewiesen |
| T3 | Verfeinerungserhalt, Präfix-Version mit Erweiterbarkeit | `system_guarantee_on_prefix` | bewiesen |
| T3 | beide Versionen für beliebig viele Komponenten | `compFamily_mono`, `system_guarantee_of_no_alarm_family`, `system_guarantee_on_prefix_family` | bewiesen |
| T3 | Erweiterbarkeit ist notwendig (Gegenbeispiel) | `Counterexample.extendability_needed` | bewiesen |
| T3 | Erweiterbarkeit ⇔ keine Sackgasse; Prüfung am Monitor | `extendable_iff_noDeadEnd`, `Monitor.Correct.extendable` | bewiesen |
| T4 | Schuldzuweisung | `no_false_blame`, `component_at_fault` | bewiesen |
| Lokalität | Monitor sieht nur die Kanäle der Schnittstelle | `Correct.localTo`, `IContract.*_local` | bewiesen |

Sprache: `atom`, `lag k` (Atom über der Beobachtung vor k Ticks und der aktuellen), `neg`, `conj`, `prev`, `since`, `onceWithin k`, `countWithin k n`; abgeleitet `step` (= `lag 1`), `once`, `hist`, `histWithin`. Die Semantik ist strukturell über die Formel definiert, mit einer Semantikfunktion je Operator.

Muster-Schemata in `Patterns.lean`: `invariant`, `aliveWithin`, `respondsWithin`, `notLongerThan`, `stepBounded`, `driftBounded`, `atLeastWithin`, `atMostWithin`, `backedBy`. Beispiele mit ausführbaren Prüfungen in `Examples.lean`.

Noch offen im Lean-Projekt:

- Komposition läuft über die globale Kanalbelegung; Verträglichkeit der Schnittstellen (disjunkte Ausgänge, Verschaltung) ist nicht modelliert.
- Dass eine Formel nur die Kanäle beobachtet, die ihre Atome lesen (`Observes` für `Fml`), ist nicht bewiesen; `IContract` verlangt die Eigenschaft bisher als Voraussetzung.
- Erweiterbarkeit ist auf Sackgassenfreiheit endlicher Präfixe zurückgeführt; eine automatische Prüfung für konkrete Muster-Instanzen (Erreichbarkeitsanalyse auf dem Produkt der Monitore) gibt es noch nicht.
- Anbindung des kompilierten Monitors an ROS 2 ist nicht erprobt.

Offener Modellierungspunkt im Paper: Die Annahme eines komponierten Contracts bezieht sich auf Ausgänge, Definition 1 beschränkt Annahmen auf Eingänge.

## Getroffene Entscheidungen (22.11.2026)

### Zuschnitt

| Thema | Entscheidung | Begründung |
|---|---|---|
| Hierarchietiefe | System → Komponente ausarbeiten, SoS als Ausblick | Theorie ist ebenenunabhängig; zweistufiges Beispiel passt auf 16 Seiten |
| Beweiswerkzeug | Lean 4 | Gerüst baut, Sätze sind algebraisch, Lean kompiliert zu C |
| Titel | mit „AI-Enabled“ | SA4AI in der Themenliste; Muster und Evaluation sind KI-spezifisch |
| Satz zentral = verteilt | bleibt, kurz als Lemma | bereits bewiesen; rechtfertigt verteilte Platzierung |

### Formaler Kern

| Thema | Entscheidung | Begründung |
|---|---|---|
| Contract-Sprache | Past-Time-Operatoren plus beschränkte Zeitfenster; Aggregate als vorberechnete atomare Signale | deckt Latenz, Rate, Liveliness, zeitliche Konsistenz; beschränkter Speicher; Beweis machbar |
| Schnittstellen | explizite Kanäle mit syntaktischer Schnittstelle (I ▷ O), im Paper und in Lean | nötig für die Aussage, welcher Monitor welche Kanäle beobachtet |
| Verfeinerungssatz | Präfix-Version mit Erweiterbarkeitsbedingung beweisen, Bedingung als Befund herausstellen | Laufzeitaussage sonst formal nicht gedeckt |
| Schuldzuweisung | als Satz, in Lean bewiesen | formales Gegenstück zu RQ3 |

### Umsetzung und Evaluation

| Thema | Entscheidung | Begründung |
|---|---|---|
| Ausführung | der Lean-Monitor selbst läuft (zu C kompiliert) hinter einem dünnen ROS-2-Knoten | bewiesener Code ist ausgeführter Code; fehlende harte Echtzeit als Limitation |
| Daten | nuScenes (mini bzw. val) als rosbag2 durch die Autoware-LiDAR-Perzeption; Rückfall auf Autoware-Beispieldaten (driving_log_replayer), falls die Sensor-Anpassung bis Mitte Januar 2027 nicht läuft | akzeptierter Benchmark plus reale Architektur |
| Katalog RQ1 | drei Quellen, etwa 30–40 Anforderungen: Taxonomie ECSA 2025, Autoware-Dokumentation, Literatur zur Überwachung von ML-Perzeption | einzelne Quelle wäre angreifbar |
| Fehlermodell | sechs Klassen auf Topic-Ebene (Ausfall, Verzögerung, eingefrorene Ausgabe, Wert außerhalb des Bereichs, Konfidenzeinbruch, fehlende/zusätzliche Objekte), je an Eingang und Ausgang | deckt Zeit und Plausibilität; Injektionsort ist Referenz für die Schuldzuweisung |

### Infrastruktur

| Thema | Entscheidung | Begründung |
|---|---|---|
| Zeitmodell | feste Tickdauer (z. B. 10 ms), Abtast-Wrapper liefert je Kanal und Tick eine Nachricht oder ⊥ | entspricht dem getakteten FOCUS-Modell; Abtastung als Threat to Validity |
| Mathlib | nein, nur Lean-Standardbibliothek | schneller Build, stabil, kleines Artefakt |
| Versionierung | Git-Repository `AImotion-Bavaria/contract-monitors` (privat), lokal außerhalb von OneDrive geklont; OneDrive als Ablage für PDFs | Git und OneDrive vertragen sich schlecht; anonymisierter Spiegel für die Einreichung |
| Arbeitsweise | alle Änderungen direkt auf `main` | ein Autor, ein Stand; kein Umschalten zwischen Branches |

### Einordnung der Erweiterbarkeit (22.11.2026)

- Der Begriff ist nicht neu (bad prefix, frühestmögliche Erkennung, machine closure). Das Paper beansprucht deshalb nicht den Begriff, sondern seine Rolle für die Übertragung der Verfeinerung auf endliche Beobachtungen. Details und offene Recherchen in `notes/extendability-literature.md`.
- Nächstliegende verwandte Arbeit: Luckcuck et al. (Contracts und Monitore für ROS-Knoten); Volltext ist noch zu lesen.
- Neue Literatureinträge stehen vorerst in `paper/refs-new.bib` und sind nach Prüfung in `refs.bib` zu übernehmen.

### Messung für RQ1 (22.11.2026)

- Der Katalog wird geteilt: Die 35 Einträge des ersten Durchgangs sind der Entwurfssatz, an dem die Sprache geformt wurde. Gemessen wird an einem zurückgehaltenen Satz aus Quellen, die beim Sprachentwurf nicht ausgewertet waren (Kandidat: ISO/PAS 8800). Der zurückgehaltene Satz wird erst eingestuft, wenn die Sprache eingefroren ist.

### Spracherweiterung nach dem RQ1-Katalog (22.11.2026)

- Zählen im Fenster und Vergleich über k Ticks sind ergänzt, weil der Katalog beide Lücken zeigte. Aussagen je Objekt bleiben außerhalb und sind als Grenze benannt.

### Abschnitt 5 (22.11.2026)

- Erweiterbarkeit steht prominent: eigene Definition, Gegenbeispiel als Example, Präfix-Satz als Hauptsatz.
- Der Verfeinerungssatz ist für beliebig viele Komponenten formuliert und bewiesen.

### Laufendes Beispiel und Muster (22.11.2026)

- Laufendes Beispiel: Autoware-Perzeption als System mit den Komponenten Detektion, Tracking, Prädiktion; Eingang Punktwolke und Ego-Zustand, Ausgang prädizierte Objekte.
- Alle ausdrückbaren Muster bleiben im Paper (Tabelle in Abschnitt 3.1): Eingangs-Liveliness, Eingangs-Gültigkeit, ODD-Bedingung, Sensorzustand, Antwortzeit, Ausgangs-Liveliness, Wertebereich, Konfidenz, zeitliche Konsistenz, eingefrorene Ausgabe, Stufen-Konsistenz, Vollständigkeit im Nahbereich; Sensor-Konsistenz als vorberechnetes Signal.
- Sprache um ein zweistelliges Atom ergänzt, damit zeitliche Konsistenz und eingefrorene Ausgabe innerhalb des Beweises liegen.
- Die Sprache (Syntax, Semantik) steht in Abschnitt 3, Abschnitt 4 behandelt nur noch Synthese und Korrektheit.

## Folgen und offene Punkte aus den Entscheidungen

- Lean-Umbau erledigt bis auf die oben unter „Noch offen“ genannten Punkte.
- nuScenes ist nur nicht-kommerziell lizenziert: Das Artefakt enthält Skripte und Konfiguration, nicht die Daten.
- nuScenes-ODD-Annotationen als mögliche Referenz für ODD-Annahmen prüfen; bei Verwendung auf die doppelt anonyme Begutachtung achten.
- Tickdauer festlegen, sobald die Topic-Raten der Perzeptionskette bekannt sind.

## Ordnerstruktur

- `paper/` – LaTeX (LNCS)
  - `main.tex` – Präambel, Titel, `\input`-Liste
  - `macros.tex` – alle eigenen Definitionen
  - `include/` – je Kapitel eine Datei (`abstract`, `introduction`, …), eingebunden per `\input{include/…}`
  - `figures/` – TikZ-Abbildungen, nur der `tikzpicture`-Anteil; `figure`-Umgebung und Caption stehen im Kapitel
  - `refs.bib`
- `lean/` – Lean-4-Projekt `ContractMonitors`
- `notes/` – diese Notiz
- `978-3-032-02138-0_11.pdf` – ECSA-2025-Paper
