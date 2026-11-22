# Erweiterbarkeit: Einordnung in die Literatur

Stand: 22.11.2026. Ergebnis einer ersten, begrenzten Recherche (neun Suchanfragen, Abstracts und Auszüge, keine Volltextlektüre).

## Frage

Ist die Bedingung „Erweiterbarkeit“ (Abschnitt 5: jeder Präfix, auf dem das Präfix-Prädikat durchgehend galt, lässt sich zu einer unendlichen Historie fortsetzen, auf der es für immer gilt) neu, oder ist sie unter anderem Namen bekannt?

## Ergebnis

**Der Begriff ist nicht neu.** Er fällt mit klassischen Begriffen zusammen. Neu könnte seine Rolle sein: als genaue Bedingung dafür, dass eine zur Entwurfszeit bewiesene Contract-Verfeinerung auf die endlichen Beobachtungen der Komponenten-Monitore übertragbar ist, samt Notwendigkeit, Charakterisierung und Mechanisierung. Eine Arbeit, die genau dieses Übertragungsresultat formuliert, habe ich nicht gefunden; die Recherche war dafür aber nicht erschöpfend.

## Verwandte Begriffe

| Begriff | Quelle | Bezug zu unserer Bedingung |
|---|---|---|
| Bad prefix | Kupferman, Vardi: Model Checking of Safety Properties, FMSD 19(3), 2001 | Ein Präfix, dessen sämtliche Fortsetzungen die Eigenschaft verletzen. Eine Sackgasse ist ein bad prefix von □p, den p selbst noch nicht zurückweist. |
| Frühestmögliche Erkennung | Bauer, Leucker, Schallhart: Runtime Verification for LTL and TLTL, TOSEM 20(4), 2011 | Deren Monitore weisen jeden minimalen bad prefix zurück. Erweiterbarkeit von p heißt genau: Der einfache Monitor für p tut das bereits, ohne Vorausschau. |
| Machine closure | Abadi, Lamport: Conjoining Specifications, TOPLAS 17(3), 1995 | Jedes endliche Verhalten, das den Sicherheitsteil erfüllt, lässt sich zu einem Verhalten fortsetzen, das die ganze Spezifikation erfüllt. Gleiche Form, dort für das Verhältnis von Sicherheits- und Lebendigkeitsteil. |
| Receptiveness / nonblocking | Literatur zu offenen Systemen und Schnittstellentheorien | Verwandte Forderung für offene Systeme: Die Umgebung kann die Komponente nicht in eine Lage bringen, aus der sie nicht weiterkommt. |
| Konsistenz eines Contracts | Benveniste et al.: Contracts for System Design, 2018 | Schwächer: Konsistenz verlangt nur, dass es überhaupt eine Implementierung gibt. Unser Gegenbeispiel ist ein inkonsistenter Contract; Erweiterbarkeit verlangt mehr, nämlich Fortsetzbarkeit von jedem guten Präfix aus. |

Die Äquivalenz „p ist erweiterbar ⇔ p weist genau die bad prefixes von □p zurück“ folgt direkt aus unserem Satz über Sackgassen.

## Nächstliegende verwandte Arbeiten zu Contracts und Monitoren

| Arbeit | Inhalt laut Abstract | Abgrenzung (vorläufig) |
|---|---|---|
| Luckcuck, Farrell, Ferrando, Cardoso, Dennis, Fisher: A Compositional Approach to Verifying Modular Robotic Systems (arXiv:2208.05507; Robotics and Autonomous Systems) | A/G-Contracts in Prädikatenlogik für ROS-Knoten, Inferenzregeln zur Herleitung von Systemeigenschaften aus Knoten-Contracts, eigene Contract-Sprache RCL, automatische Übersetzung in ausführbare Monitore | **Die nächstliegende Arbeit.** Am Volltext geprüft, siehe eigener Abschnitt unten. |
| Sokolsky, Zhang, Lee, McDougall: Monitoring Assumptions in Assume-Guarantee Contracts (PrePost 2016, EPTCS 208) | Garantien werden vor der Auslieferung verifiziert, Annahmen danach zur Laufzeit überwacht; Konstruktion und Verifikation der Annahme-Monitore | Überwacht nur Annahmen einzelner Komponenten; keine Hierarchie. |
| Xu, Ng, Easwaran: Automatic Generation of Hierarchical Contracts for Resilience in Cyber-Physical Systems (RTCSA 2019) | Hierarchie von A/G-Contracts zur Überwachung nichtfunktionaler Eigenschaften; automatische Zerlegung eines Wurzel-Contracts | Hierarchische Überwachung, aber für numerische nichtfunktionale Größen und ohne formalen Korrektheitsnachweis der Monitore. |
| Cimatti, Grosen, Larsen, Tonetta, Zimmermann: Exploiting Assumptions for Effective Monitoring of Real-Time Properties under Partial Observability (arXiv:2409.05456) | Annahmen über das Systemverhalten ermöglichen frühere Verdikte und Überwachung nicht beobachtbarer Teile | Nutzt Annahmen zur Vorausschau eines einzelnen Monitors; keine Verfeinerungshierarchie. |

## Luckcuck et al. im Detail

Geprüft an arXiv:2208.05507v3 (HTML-Fassung), ausgewertet über eine automatische Zusammenfassung mit gezielten Fragen; die Formeldarstellung in §3.2 war in der Quelle unvollständig. Vor der Einreichung sind die Aussagen an der Zeitschriftenfassung zu bestätigen.

| Aspekt | Luckcuck et al. | Unser Paper |
|---|---|---|
| Contract-Form | A(i) ⇒ ◇G(o): Eine Eingabe führt irgendwann zu einer Ausgabe; keine Zeitschranken (§3.2) | Annahme und Garantie als Sicherheitseigenschaften über getakteten Strömen, mit Zeitfenstern |
| Herleitung auf Systemebene | Kalkül mit Regeln R1 bis R3 (Kette, Verzweigung, Vereinigung) plus R4 für Schleifen; manuell angewendet; Korrektheitsbeweise „for brevity“ ausgelassen (§3.4) | Verfeinerung und Komposition mit mechanisierten Beweisen |
| Verfeinerung | kein Verfeinerungsoperator; Hierarchie nur als Abstraktion zu zusammengesetzten Knoten (§3.1) | Verfeinerungsrelation als Kern |
| Monitore | nur für Garantien; Werkzeug Vanda übersetzt nach ROSMonitoring/RML (§3.6); kein Korrektheitsbeweis der Übersetzung | Synthese mit bewiesener Korrektheit; der bewiesene Monitor wird ausgeführt |
| Stille Monitore ⇒ Systemeigenschaft | informell behauptet (§3) | präzisiert, bewiesen, und als nur unter Sackgassenfreiheit gültig gezeigt |
| Annahmen und Schuld | Annahmen werden nicht überwacht; eine Garantieverletzung ist von einer Annahmeverletzung nicht unterscheidbar; Annahme-Monitore sind Future Work (§6) | getrennte Annahme- und Garantie-Monitore mit Schuldsatz |
| Mechanisierung | keine; Automatisierung des Kalküls mit Vampire als Future Work (§3.4) | Lean 4 |

Einordnung: Die Arbeit behauptet informell genau die Aussage, die unser Präfix-Satz präzisiert. Das stützt die Motivation und zeigt zugleich, wo unser Beitrag liegt. Offen bleibt bei ihnen, wie ein Monitor eine „irgendwann“-Garantie auf einem endlichen Lauf widerlegen kann; dazu fand sich keine Aussage.

Stärken der Arbeit, die wir nicht haben: Prädikatenlogik über Daten, heterogene Verifikation der Knoten (Modellprüfung, Hoare-Logik, Dafny), Fallstudie an einem realen Rover.

## Folgen für das Paper

- Die Einleitung behauptet nicht mehr, die Bedingung zu „identifizieren“. Der Beitrag lautet: Die Übertragung der Verfeinerung auf endliche Beobachtungen braucht Sackgassenfreiheit; das ist notwendig, charakterisiert und mechanisiert.
- Abschnitt 5 verknüpft „dead end“ mit „bad prefix“ und der frühestmöglichen Erkennung.
- Related Work hat einen neuen Absatz zu Sicherheit und endlichen Beobachtungen und nennt Luckcuck et al., Sokolsky et al. und Xu et al.

## Offen

- Aussagen zu Luckcuck et al. an der Zeitschriftenfassung bestätigen (bisher arXiv v3 über automatische Zusammenfassung).
- Gezielt nach „circular assume-guarantee reasoning soundness safety“ (McMillan; Alur und Henzinger; Jonsson und Tsay) suchen: Dort treten Sicherheits- und Abschlussbedingungen als Voraussetzung der Kompositionsregeln auf.
- Literatur zu Schnittstellentheorien (interface automata, modal specifications) auf eine Entsprechung der Bedingung prüfen.
