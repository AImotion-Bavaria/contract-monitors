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
| Luckcuck, Farrell, Ferrando, Cardoso, Dennis, Fisher: A Compositional Approach to Verifying Modular Robotic Systems (arXiv:2208.05507; Robotics and Autonomous Systems) | A/G-Contracts in Prädikatenlogik für ROS-Knoten, Inferenzregeln zur Herleitung von Systemeigenschaften aus Knoten-Contracts, eigene Contract-Sprache RCL, automatische Übersetzung in ausführbare Monitore | **Die nächstliegende Arbeit.** Nach Abstract keine mechanisierte Korrektheit der Monitore und keine Aussage über endliche Beobachtungen; das ist am Volltext zu prüfen. |
| Sokolsky, Zhang, Lee, McDougall: Monitoring Assumptions in Assume-Guarantee Contracts (PrePost 2016, EPTCS 208) | Garantien werden vor der Auslieferung verifiziert, Annahmen danach zur Laufzeit überwacht; Konstruktion und Verifikation der Annahme-Monitore | Überwacht nur Annahmen einzelner Komponenten; keine Hierarchie. |
| Xu, Ng, Easwaran: Automatic Generation of Hierarchical Contracts for Resilience in Cyber-Physical Systems (RTCSA 2019) | Hierarchie von A/G-Contracts zur Überwachung nichtfunktionaler Eigenschaften; automatische Zerlegung eines Wurzel-Contracts | Hierarchische Überwachung, aber für numerische nichtfunktionale Größen und ohne formalen Korrektheitsnachweis der Monitore. |
| Cimatti, Grosen, Larsen, Tonetta, Zimmermann: Exploiting Assumptions for Effective Monitoring of Real-Time Properties under Partial Observability (arXiv:2409.05456) | Annahmen über das Systemverhalten ermöglichen frühere Verdikte und Überwachung nicht beobachtbarer Teile | Nutzt Annahmen zur Vorausschau eines einzelnen Monitors; keine Verfeinerungshierarchie. |

## Folgen für das Paper

- Die Einleitung behauptet nicht mehr, die Bedingung zu „identifizieren“. Der Beitrag lautet: Die Übertragung der Verfeinerung auf endliche Beobachtungen braucht Sackgassenfreiheit; das ist notwendig, charakterisiert und mechanisiert.
- Abschnitt 5 verknüpft „dead end“ mit „bad prefix“ und der frühestmöglichen Erkennung.
- Related Work hat einen neuen Absatz zu Sicherheit und endlichen Beobachtungen und nennt Luckcuck et al., Sokolsky et al. und Xu et al.

## Offen

- Volltext von Luckcuck et al. lesen: Wie werden Systemeigenschaften hergeleitet, und gilt die Herleitung für endliche Läufe?
- Gezielt nach „circular assume-guarantee reasoning soundness safety“ (McMillan; Alur und Henzinger; Jonsson und Tsay) suchen: Dort treten Sicherheits- und Abschlussbedingungen als Voraussetzung der Kompositionsregeln auf.
- Literatur zu Schnittstellentheorien (interface automata, modal specifications) auf eine Entsprechung der Bedingung prüfen.
- Bibliografische Angaben der neuen Einträge prüfen; sie stehen vorerst in `paper/refs-new.bib`.
