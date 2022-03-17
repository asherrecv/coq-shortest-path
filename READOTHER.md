# Repository

Wie kann man ein:e Anweder:in von einem Programm davon überzeugen, dass es korrekt gerechnet hat? Durch Tests lässt sich dies nicht erreichen, da ja nur endlich viele Eingaben überprüft werden. Ein:e Anwender:in könnte einer nicht getesteten Eingabe zum Opfer fallen. Eine sehr starke Korrektheitsgarantie erhalten man, indem durch formale Verifikation. Dies ist aber leider sehr aufwändig und oft sogar unmöglich. 

Eine weitere Idee ist es, das Programm zusätzlich ein auf die Ein- und Ausgabe zugeschnittenes Zertifikat ausgeben zu lassen. Dieses soll einfach überprüfbar sein und die Korrektheit der Programmausführung belegen. Das funktioniert natürlich nur, wenn ein:e Anwender:in davon überzeugt ist, dass Zertifkate im jeden Fall die Korrektheit belegen. Wenn ein:e Anwender:in überzeugt ist, muss er:sie lediglich überprüfen, ob das Zertifikat korrekt ist. Das wiederrum ist eine Aufgabe, die sich hervorragend mit einem Checker automatisieren lässt. Algorithmen, die auf diese Weise funktionieren nennt man _zertifizierende _Algorithmen_.

Beispielsweise liese sich ein Programm, was die Anzahl der Lösung einer quadratischen Gleichung im reellem Zahlenraum ausgibt folgenderweise zertifizierend gestalaten. Das Programm erwartet als Eingabe die Koeffizienten $a$, $b$ und $c$ einer quadratischen Gleichung. Neben der Anzahl der Lösungen (also keine, eine oder zwei) gibt das Program zusätzlich auch die Diskriminante $b^2 - 4ac$ aus. Die zusätzliche Ausgabe (die Diskrimante) dient als Zertifikat. Wenn ein:e Anwender:in grundlegendes Verständnis von mathematischen Zusammenhängen hat, versteht er:sie, was das Vorzeichen einer Diskrimnante für die der Programmausgabe (also der Anzahl der Lösungen) bedeutet bedeuetet. Außerdem ist es einach zu Überprüfen, ob das Zertifikat zur Ein- und Ausgabe passt. Zusammen kann sich der:die Anwender:in einfach von der Korrektheit einer Berechnung überzeugen, ohne das Programm selbst verstehen zu müssen.

Interessant wird es formale Verifikation und zertifizierenden Algorithmen zu kombinieren. Zum einen lässt sich natürlich ein Checker formal verifizieren. Zum anderen lässt sich aber auch die Aussage das Zertifikat für eine Ein- und Ausgabe impliziert immer die Korrekheit der Berechnung formal beweisen. Diese Eingeschaft nennt man auch _Zeugeneigenschaft_. Dadurch wird einer:em Anwender:in die Last genommen, die Eigenschaft selber vestehen zu müssen. Es muss lediglich dem formalen verifizierten Beweis der Zeugeneigenschaft vertraut werden.  Die Korrektheit einer Berechnung ist damit -- bei Akzeptanz des Checkers -- durch einen maschinenüberprüfbaren Beweis abgesichert und so vertrauenswürdig, als wäre die Berechnung von einen formal verifizierten Algorithmus erfolgt. Das nennt man auch _formale Instanzkorrektheit_ [[2]](#2).

Neben den bisher betrachteten klassischen Algorithmen und Programmen, stellt sich die Frage ob sich der Ansatz auch auf verteilte Algorithmen übertragen lässt. Für den verteilten Bellman-Ford-Algorithmus (und einige mehr) zur Berechnung kürzester Pfade in einem Netzwerk  lässt sich diese Frage bejahen [[3]](#3).  Die Idee ist e dabei, das jede Komponente des Netzwerks berechnet ein lokales Zertifikat berechnet. Alle lokalen Zertifikate zusammen sollen die Korrektheit des verteilten Ergebnisses belegen (_verteilte Zeugeneigenschaft_). Die Überprüfung des verteilten Ergebnisses, erfolgt ebenfalls verteilt durch lokale Checker, welche jeder Komponente zugewiesen werden. Das verteilte Ergebnis ist genau dann korrekt, wenn alle lokalen Checker akzeptieren. 

Dieses Repository enthält die Coq-Formalisierung der formalen Insztanzkorrektheit der verteilten Überprüfung eines verteilten Netzwerkalgorithmus zur Berechnung kürzester Pfade. Zunächst wird die Zeugeneigenschaft im klassischem Setting bewiesen und dann auf das verteilte Setting übertragen. 



# 1. Überprüfung einer Kürzesten-Wege-Funktion

Stellen wir uns vor, wir haben einen Graphen mit einem ausgezeichnet Startknoten und wollen die kürzeste Pfade zu allen anderen Knoten berechnen lassen. Das heißt wir suchen einen Kürzeste-Wege-Baum für den Graphen mit dem angegeben Startknoten. Das lässt sich zum Beispiel mit dem Algorithmus von Dijkstra lösen. Wie können wir den von Algorithmus ausgegeben Baum auf seine Korrektheit überprüfen? Welche Zeugeneigenschaft eignet sich hierfür? In diesem Abschnitt beschreiben wir, wie sich ein leicht abgewandelte Ausgabe zertifizieren lässt: Die Kürzeste-Wege-Funktion. Eine Kürzeste-Wege-Funktion und ein Kürzester-Wege-Baum lassen sich leicht ineinander umwandeln.

## 1.1. Definitionen

Sei $G=(V,E,s)$ ein ungerichteter, zusammenhängender Graph mit einem ausgezeichneten Startknoten $s\in V$ und $c:E\to \mathbb{N}_{>0}$ eine Kantenbewertungsfunktion.

_Definition_ (__Pfad__) Ein Pfad $p$ von einem Knoten $s\in V$ zu einem Knoten $t\in V$ ist eine Folge von Knoten $(v_1,\ldots, v_n)$, so dass $v_1=s$, $v_n=t$ und $\{v_i,v_{i+1}\}\in E$ für alle $1\leq i \leq n-1$.

_Definition_ (__Pfadkosten__) Die Pfadkosten eines Pfades $p=(v_1,\ldots,v_n)$ entsprechen der Summe der Kantengewichte entlang des Pfades, also dem Wert $\sum_{1\leq i \leq n -1 } c\left(\{v_i,v_{i+1}\}\right)$.

_Definition_ (__Kürzeste-Wege-Funktion__) Eine Funktion $\delta: V\to \mathbb{N}_{\geq 0}$ heißt Kürzeste-Wege-Funktion des Graphen $G$, wenn $\delta(v)=\min\{ \text{Pfadkosten von \(p\)} \mid \text{\(p\) Pfad von \(s\) nach \(v\)}\}$ für alle $v\in V$.


## 1.2. Zeugeneigenschaft

Eine Funktion $D:V\to \mathbb{N}_{\geq 0}$ kann einfach darauf überprüft werden, ob sie eine Kürzeste-Wege-Funktion für den Graph $G$ ist. Dafür ist es hinreichend, $D$ auf drei Eigenschaften zu überprüfen. Das heißt es bedarf zur Überprüfung der Ergebniskorrektheit, keines zusätzlichen mathematisches Artefakts, welches als Zeuge fungiert -- die Ausgabe zertifiziert sich gewissermaßen selbst.

\begin{align*}
    D(s)                                                                & = 0                  & \text{\footnotesize(Starteigenschaft)}      \\
    \forall \{u,v\} \in E : D(v)                                        & \leq D(u)+c(\{u,v\}) & \text{\footnotesize(Dreiecksungleichung)}   \\
    \forall v\in V\setminus\{s\}: \exists u \in V : \{u,v\}\in E : D(v) & =D(u)+c(\{u,v\})     & \text{\footnotesize(Ausgleichseigenschaft)} \\
\end{align*}


Dann ist für alle $v\in V$

$$
D(v)=\delta(v).
$$


Wir zeigen zwei Richtungen, die zusammen die Gleichheit belegen.

\begin{itemize}
    \item 
    $\bm{D(v)\leq \delta(v)}$ \, Der Beweis erfolgt per Induktion über die Pfadlänge eines kürzesten Pfades.
    \begin{description}
        \item[Induktionsanfang] Ein Pfad der Länge eins, besteht nur aus dem Startknoten $s$ selbst. Dieser ist auch der eindeutige kürzeste Pfad, da aufgrund der positiven Kantengewichte alle längeren Pfade positive Kosten haben. Daraus und der Starteigenschaft folgt, dass $D(s)=\delta(s)=0$.
        \item[Induktionsschritt] Wir haben einen kürzesten Pfad $(v_1,\ldots,v_{i+1})$ der Länge $i+1$. Wir nehmen an, dass für Pfade der Länge $i$ gilt, dass $D(v_i)\leq \delta(v_i)$. Weiterhin gilt wegen der optimalen Substruktur von kürzesten Pfaden, dass $\delta(v_{i+1})=\delta(v_i)+c(\{v_i,v_{i+1}\})$.
        \begin{align*}
            D(v_{i+1}) & \leq D(v_i) + c(\{v_i,v_{i+1}\})       & \text{(Dreiecksungleichung)}  \\
                       & \leq \delta(v_i) + c(\{v_i, v_{i+1}\}) & \text{(Induktionsannahme)}    \\
                       & = \delta(v_i+1)                        & \text{(optimale Substruktur)} 
        \end{align*}
    \end{description}
     \item 
     $\bm{D(v)\geq \delta(v)}$ \, Zur Erzeugen eines Widerspruchs nehmen wir an, dass es ein $v$ gibt, sodass $D(v)<\delta(v)$. Von allen $v$ mit $D(v)<\delta(v)$, sei $v$ so gewählt, dass $D(v)$ minimal ist (das heißt für alle $v'$ mit $D(v') < D(v)$ ist $D(v')\geq\delta(v')$). Da $D(s)=\delta(s)=0$, wissen wir, dass $v\neq s$. Dann muss es wegen der Ausgleichseigenschaft, einen Knoten $u$ geben, sodass $D(v)=D(u)+c(\{u,v\})$.  Aufgrund der positiven Kantengewichte ist $D(u) < D(v)$. Wegen unser Wahl von $v$, muss $D(u)\geq \delta(u)$ sein. Aufgrund der ersten Richtung gilt aber auch $D(u)\leq \delta(u)$. Zusammen ist also $D(u)=\delta(u)$. Mit der Ausgleichskante, können wir einen Pfad nach $v$ mit Kosten $\delta(u)+c(\{u,v\})$ konstruieren. Ein kürzester Pfad nach $v$ hat Kosten $\delta(v)$. Deswegen muss $\delta(v) \leq \delta(u)+c(\{u,v\})$ sein. Zusammen gilt:
        \begin{align*}
            \delta(v) & \leq \delta(u) + c(\{u,v\}) &                        \\
                      & = D(u) + c(\{u,v\})         & (D(u)=\delta(u))       \\
                      & = D(v),                     & (D(v)=D(u)+c(\{u,v\})) 
        \end{align*}
     was ein Widerspruch zur Annahme darstellt.
\end{itemize}


# 1.3. Verteilte Überprüfung eines Kürzesten-Wege-Netzwerks

Wie kann das Ergebnis des verteilten Bellman-Ford-Algorithmus auf Korrektheit überprüft werden? Wir beobachten, dass zur Feststellung der Gültigkeit der Dreiecksungleichung und der Ausgleichseigenschaft, ausschließlich die Funktionswerte der Nachbarschaft benötigt werden. Die Feststellung der Starteigenschaft benötigt keine zusätzliche Information. Dies motiviert die Definition des lokalen Zertifikat einer Komponente, als die Menge der berechneten Werte der Nachtbarschaft. Dieser wird vom lokalen Checker zur Teilüberprüfung des globalen Ergebnisses verwendet. Beispielsweise hält nach der Ausführung des zertifizierenden verteilten Bellman-Ford-Algorithmus auf dem Netzwerk aus Abbildung, die Komponente $e$ die Werte $y_b$ und $y_c$ als lokales Zertifikat. Der Checker der Komponente $e$ muss überprüfen, ob die Dreiecksungleichung und Ausgleichseigenschaft in der Nachbarschaft erfüllt sind. Die Überprüfung der Starteigenschaft entfällt, da $e$ nicht die Quelle ist. Zur Überprüfung der Dreiecksungleichung müssen die Ungleichungen $y_d \leq y_b +8$ und $y_d \leq y_c + 1$ überprüft werden. Weiterhin muss der lokale Checker zur Überprüfung der Ausgleichseigenschaft feststellen, ob eine der Ungleichung tatsächlich eine Gleichheit ist. Hier stellt er fest, dass $y_d = y_c + 1$.

\begin{tikzpicture}%[every node/.style={fill,circle,inner sep=1pt}]
    \node [label=left:{$\{y_a \mapsto 0, y_c \mapsto 5\}$}] (D) at (-4.0, -1) [circle,draw] {$d$};
    \node [label=left:{$\{y_b \mapsto 2, y_c \mapsto 5, y_d \mapsto 7\}$}] (A) at (-2.5, +1) [circle,draw] {$a$};
    \node [label=below:{$\{y_a \mapsto 0, y_b \mapsto 2, y_d \mapsto 7, y_e \mapsto 6\}$}](C) at (-1.0, -1) [circle,draw] {$c$};
    \node [label=right:{$\{y_a \mapsto 0, y_c \mapsto 5, y_e \mapsto 6\}$}] (B) at (+0.5, +1) [circle,draw] {$b$};
    \node [label=right:{$\{y_b \mapsto 2, y_c \mapsto 5\}$}] (E) at (+2.0, -1) [circle,draw] {$e$};
    \draw (D) to node[above] {$10$} (A);
    \draw (D) to node[above] {$2$} (C);
    \draw (A) to node[above] {$5$} (C);
    \draw (A) to node[above] {$2$} (B);
    \draw (C) to node[above] {$1$} (E);
    \draw (C) to node[above] {$3$} (B);
    \draw (B) to node[above] {$8$} (E);
\end{tikzpicture}

# 2. Coq-Formalisierung

## 2.1. Sequentielle Zeugeneigenschaft

Die Knotenmenge wird als dependent pair definiert.

```Coq
Definition set n := { x : nat | x < n }.
```

Darauf aufbauend definieren wir auf den Record `graph`, zur Repräsentation eines endlichen, gewichteten Graphen:

```Coq
Record graph : Set := mk_graph {
  V : nat;
  E : (set V) -> (set V) -> nat;
  s : (set V)
}.
```

Induktives Prädikat für Pfad in einem Graphen repräsentiert:

```Coq
Inductive path (g : graph) : 
   list (set g.(V)) -> set g.(V) -> set g.(V) -> nat -> Prop :=
| zerop : forall v,
    path g (v::nil) v v 0 
| consp : forall u v, 
    g.(E) u v > 0 ->
      forall p sv d, path g (u::p) u sv d ->
        path g (v::u::p) v sv (d + g.(E) u v).
```

Definition für einen kürzesten Pfad:

```Coq
Definition shortest_path (g : graph) (p : list (set g.(V))) 
  (v sv : set g.(V)) (d : nat) : Prop :=
    path g p v sv d /\ forall p' d', path g p' v sv d' -> d <= d'.
```

Hilfslemma optimale Substruktur von kürzesten Pfaden:

```Coq
Lemma shortest_path_opt_substructure : forall u v p d, 
  g.(E) u v > 0 ->
    shortest_path g (v::u::p) v g.(s) (d + g.(E) u v) -> 
      shortest_path g (u::p) u g.(s) d.
``` 

Definition der Voraussetzungen der Zeugeneigenschaft:
```Coq
Variable dist : set g.(V) -> nat.

Definition start_prop :=
  dist g.(s) = 0.
Definition trian_prop := forall u v, 
  g.(E) u v > 0 -> dist v <= dist u + g.(E) u v.
Definition justf_prop := forall v,
  v <> g.(s) -> exists u, g.(E) u v > 0 /\ dist v = dist u + g.(E) u v.
```

Sequentielle Zeugeneigenschaft:
```Coq
Hypothesis Hstart_prop : start_prop.
Hypothesis Htrian_prop : trian_prop.
Hypothesis Hjustf_prop : justf_prop.

Theorem witness_prop : forall v,
  dist v = delta v.
Proof.
intro v.
  apply le_antisym.
  apply dist_leq_delta.
  apply dist_geq_delta.
Qed.
```

## 2.2. Verteilte Zeugeneigenschaft

Definition einer Netzwerkcomponente mit eindeutigem Bezeichner $i$, der Nachbarschaftsmenge $E_i$ und der Information, ob die Komponente der Startknoten ist $is_s$.
```Coq
Record component : Set := mk_component {
  is_s  : bool;
  i     : (set n);             
  E_i   : (set n) -> nat
}.
```

Definition der Voraussetzungen der verteilten Zeugeneigenschaft:

```Coq
Definition local_start_prop (c : component) : Prop :=
  dist c.(i) = 0.

Definition local_trian_prop (c : component) : Prop :=
  forall j, c.(E_i) j > 0 -> dist c.(i) <= dist j + c.(E_i) j.

```Coq
Definition local_justf_prop (c : component) : Prop :=
  exists j, c.(E_i) j > 0 /\ dist c.(i) = dist j + c.(E_i) j.

Definition local_wtnss_prop (c : component) : Prop :=
  (c.(is_s) = true -> local_start_prop c /\ local_trian_prop c) /\ 
  (c.(is_s) = false -> local_trian_prop c /\ local_justf_prop c).
```

Verteilte Zeugeneigenschaft:
```Coq
Theorem dist_eq_network_delta : forall (v : set network_g.(V)),
  dist v = delta_network_g v.
```

# References
<a id="1">[1]</a>
R.M. McConnell, K. Mehlhorn, S. Näher und P. Schweitzer: Certifying algorithms. Computer Science Review, 5(2):119 – 161, 2011.

<a id="2">[2]</a>
Christine Rizkallah: Verification of Program Computations. Dissertation, Universität des Saarlandes, Saarbrücken, 2015.

<a id="3">[3]</a>
Kim Völlinger und Wolfgang Reisig: Certifcation of Distributed Algorithms Solving Problems with Optimal Substructure. In: Software Engineering and Formal Methods, 2015.