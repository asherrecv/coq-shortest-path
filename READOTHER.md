# Einleitung

Eine herausfordernde Aufgabe des Software Engineering ist es die Korrektheit eines Programms sicherzustellen. Bekannte Methoden sind das Testen und die formale Verifikation. Beim Testen wird für eine Stichprobe der möglichen Eingaben eines Programms gezeigt, dass es korrekt ist. Schwierig ist es hierbei eine möglichst repräsentative Stichprobe zu wählen. Für alle Eingaben außerhalb der Stichprobe erhalten wir keine Korrektheitsgarantie. Eine stärkere Korrektheitsgarantie erhalten wir bei der formalen Verifikation. Verifizieren wir ein Programm, so beweisen wir, dass es für alle Eingaben korrekt ist. Die formale Verifikation eines Programms ist jedoch oft zu aufwändig oder sogar unmöglich. Zum einen müssen wir die Korrektheit des Algorithmus zeigen, zum anderen müssen wir zeigen, dass er korrekt implementiert ist. Vor allem der Beweis der Korrektheit der Implementierung ist oft praktisch nicht durchführbar.

Mehlhorn et. al. [[1]](#1) schlagen das Konzept des _zertifizierenden Algorithmus_ als weiteren Ansatz zur Qualitätssicherung von Software vor. Ein zertifizierender Algorithmus berechnet zu jedem Ergebnis, ein einfach zu überprüfendes Zertifikat, welches die Korrektheit des Ergebnisses impliziert. Der Benutzer eines zertifizierenden Algorithmus, kann sich anhand des Zertifikats von der Korrektheit des Ergebnisses überzeugen. Die Zertifikatsüberprüfung kann durch einen  Entscheidungsalgorithmus -- dem Checker erfolgen. Auf diese Weise kann der Benutzer Gewissheit über die Korrektheit des Ergebnisses erlangen, ohne dem Algorithmus vertrauen zu müssen. 

Rizkallah [[2]](#2) entwickelt aufbauend auf dem Konzept des zertifizierenden Algorithmus, den Begriff der _formalen Instanzkorrektheit_. Die Idee ist es die Aussage "der Checker akzeptiert ein Zertifikat für ein Ergebnis genau dann, wenn das Ergebnis korrekt ist" mit Methoden der formalen Verifikation zu belegen. Der formale Beweise der Aussage erfolgt über zwei Schritte: Als erstes wird bewiesen, dass Zertifikate immer die Korrektheit eines Ergebnisses implizieren. Der nächste Schritt bildet der Korrektheitsbeweis der Checker-Implementation. Die Korrektheit des Ergebnisses ist damit -- bei Akzeptanz des Checkers -- durch einen maschinenüberprüfbaren Beweis abgesichert und so vertrauenswürdig, als wäre die Berechnung von einen formal verifizierten Algorithmus erfolgt.

In [[3]](#3) veschreibt Völlinger, wie ein verteilter Netzwerkalgorithmus zur Berechnung kürzester Pfade, zertifizierend gestaltet werden kann. Jede Komponente des Netzwerks berechnet ein lokales Zertifikat, sodass alle lokalen Zertifikate zusammen die Korrektheit des verteilten Ergebnisses belegen. Die Überprüfung des verteilten Ergebnisses, erfolgt ebenfalls verteilt durch lokale Checker, welche jeder Komponente zugewiesen werden. Das verteilte Ergebnis ist genau dann korrekt, wenn alle lokalen Checker akzeptieren. Völlinger bezeichnet dieses Vorgehen als den _lokalen Ansatz_. 


# Definitionen

Sei $G=(V,E,s)$ ein ungerichteter, zusammenhängender Graph mit einem ausgezeichneten Startknoten $s\in V$ und $c:E\to \mathbb{N}_{>0}$ eine Kantenbewertungsfunktion.

_Definition_ (__Pfad__) Ein Pfad $p$ von einem Knoten $s\in V$ zu einem Knoten $t\in V$ ist eine Folge von Knoten $(v_1,\ldots, v_n)$, so dass $v_1=s$, $v_n=t$ und $\{v_i,v_{i+1}\}\in E$ für alle $1\leq i \leq n-1$.

_Definition_ (__Pfadkosten__) Die Pfadkosten eines Pfades $p=(v_1,\ldots,v_n)$ entsprechen der Summe der Kantengewichte entlang des Pfades, also dem Wert $\sum_{1\leq i \leq n -1 } c\left(\{v_i,v_{i+1}\}\right)$.

_Definition_ (__Kürzeste-Wege-Funktion__) Eine Funktion $\delta: V\to \mathbb{N}_{\geq 0}$ heißt Kürzeste-Wege-Funktion des Graphen $G$, wenn $\delta(v)=\min\{ \text{Pfadkosten von \(p\)} \mid \text{\(p\) Pfad von \(s\) nach \(v\)}\}$ für alle $v\in V$,

# Überprüfung einer Kürzesten-Wege-Funktion

Ein Algorithmus zur Lösung des Kürzesten-Pfade-Problems mit einer Quelle, wie beispielsweise der Dijkstra-Algorithmus, berechnet einen Spannbaum mit der Quelle als Wurzel. Der Weg von der Wurzel zu einem Knoten des Spannbaums, hat minimale Pfadkosten. Der Spannbaum ist nicht notwendigerweise eindeutig. Aus dem Spannbaum lässt sich jedoch eine eindeutige Funktion $D:V\to \mathbb{N}_{\geq 0}$ ableiten. Die Funktionswerte entsprechen den Pfadkosten eines kürzesten Pfades. Wir beschränken uns zunächst darauf, wie diese Funktion auf ihre Korrektheit überprüft werden kann. 

# Zeugeneigenschaft

Eine Funktion $D:V\to \mathbb{N}_{\geq 0}$ kann einfach darauf überprüft werden, ob sie eine Kürzeste-Wege-Funktion für den Graph $G$ ist. Dafür ist es hinreichend, $D$ auf drei Eigenschaften zu überprüfen. 
Das heißt es bedarf zur Überprüfung der Ergebniskorrektheit, keines zusätzlichen mathematisches Artefakts, welches als Zeuge fungiert -- die Ausgabe zertifiziert sich gewissermaßen selbst.

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

# Motivation

Gemäß dem lokalen Ansatz, erfolgt die Überprüfung des verteilten Ergebnisses mithilfe lokal berechneter Zeugen durch lokale Checker. Wie kann das Ergebnis des verteilten Bellman-Ford-Algorithmus auf Korrektheit überprüft werden? Wir beobachten, dass zur Feststellung der Gültigkeit der Dreiecksungleichung und der Ausgleichseigenschaft, ausschließlich die Funktionswerte der Nachbarschaft benötigt werden. Die Feststellung der Starteigenschaft benötigt keine zusätzliche Information. Dies motiviert die Definition des lokalen Zeugen einer Komponente, als die Menge der berechneten Werte der Nachtbarschaft. Dieser wird vom  lokale Checker zur Teilüberprüfung des globalen Ergebnisses verwendet. Beispielsweise hält nach der Ausführung des zertifizierenden verteilten Bellman-Ford-Algorithmus auf dem Netzwerk aus Abbildung, die Komponente $e$ die Werte $y_b$ und $y_c$ als lokalen Zeugen. Der Checker der Komponente $e$ muss überprüfen, ob die Dreiecksungleichung und Ausgleichseigenschaft in der Nachbarschaft erfüllt sind. Die Überprüfung der Starteigenschaft entfällt, da $e$ nicht die Quelle ist. Zur Überprüfung der Dreiecksungleichung müssen die Ungleichungen $y_d \leq y_b +8$ und $y_d \leq y_c + 1$ überprüft werden. Weiterhin muss der lokale Checker zur Überprüfung der Ausgleichseigenschaft feststellen, ob eine der Ungleichung tatsächlich eine Gleichheit ist. Hier stellt er fest, dass $y_d = y_c + 1$.

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

# References
<a id="1">[1]</a>
R.M. McConnell, K. Mehlhorn, S. Näher und P. Schweitzer: Certifying
algorithms. Computer Science Review, 5(2):119 – 161, 2011.

<a id="2">[2]</a>
Christine Rizkallah: Verification of Program Computations. Dissertation,
Universität des Saarlandes, Saarbrücken, 2015.

<a id="3">[3]</a>
Kim Völlinger und Wolfgang Reisig: Certifcation of Distributed Algorithms
Solving Problems with Optimal Substructure. In: Software Engineering and
Formal Methods, 2015.