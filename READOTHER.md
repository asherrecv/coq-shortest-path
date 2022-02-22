

Sei im weiteren Verlauf des Kapitels $G=(V,E,s)$ ein ungerichteter, zusammenhängender Graph mit einem ausgezeichneten Startknoten $s\in V$. Weiterhin sei $c:E\to \mathbb{N}_{>0}$ eine Kantenbewertungsfunktion. 


Ein Pfad $p$ von einem Knoten $s\in V$ zu einem Knoten $t\in V$ ist eine Folge von Knoten $(v_1,\ldots, v_n)$, so dass $v_1=s$, $v_n=t$ und $\{v_i,v_{i+1}\}\in E$ für alle $1\leq i \leq n-1$.

Die Pfadkosten eines Pfades $p=(v_1,\ldots,v_n)$ entsprechen der Summe der Kantengewichte entlang des Pfades, also dem Wert $\sum_{1\leq i \leq n -1 } c\left(\{v_i,v_{i+1}\}\right)$.

Die Funktion $\delta: V\to \mathbb{N}_{\geq 0}$ mit der Eigenschaft $\delta(v)=\min\{ \text{Pfadkosten von \(p\)} \mid \text{\(p\) Pfad von \(s\) nach \(v\)}\}$ für alle $v\in V$, heißt Kürzeste-Wege-Funktion des Graphen $G$.

# Überprüfung einer Kürzesten-Wege-Funktion

Ein Algorithmus zur Lösung des Kürzesten-Pfade-Problems mit einer Quelle, wie beispielsweise der Dijkstra-Algorithmus, berechnet einen Spannbaum mit der Quelle als Wurzel. Der Weg von der Wurzel zu einem Knoten des Spannbaums, hat minimale Pfadkosten. Der Spannbaum ist nicht notwendigerweise eindeutig. Aus dem Spannbaum lässt sich jedoch eine eindeutige Funktion $D:V\to \mathbb{N}_{\geq 0}$ ableiten. Die Funktionswerte entsprechen den Pfadkosten eines kürzesten Pfades. Wir beschränken uns zunächst darauf, wie diese Funktion auf ihre Korrektheit überprüft werden kann. 

# Zeugeneigenschaft

Eine Funktion $D:V\to \mathbb{N}_{\geq 0}$ kann einfach darauf überprüft werden, ob sie tatsächlich identisch mit der Kürzeste-Wege-Funktion für den Graph $G$ ist. Dazu muss die Ausgabe $D$ lediglich auf drei Eigenschaften überprüft werden. In diesem Fall fällt der Zeuge mit der Ausgabe zusammen. Das heißt es bedarf zur Überprüfung der Ergebniskorrektheit, keines zusätzlichen mathematisches Artefakts, welches als Zeuge fungiert.
$$
	\begin{align*}
		D(s)                                                                & = 0                  & \text{\footnotesize(Starteigenschaft)}      \\
		\forall \{u,v\} \in E : D(v)                                        & \leq D(u)+c(\{u,v\}) & \text{\footnotesize(Dreiecksungleichung)}   \\
		\forall v\in V\setminus\{s\}: \exists u \in V : \{u,v\}\in E : D(v) & =D(u)+c(\{u,v\})     & \text{\footnotesize(Ausgleichseigenschaft)} \\
	\end{align*}
$$

	Dann ist für alle $v\in V$
$$
	\[D(v)=\delta(v).\]
$$


	Wir zeigen zwei Richtungen, die Zusammen die Gleichheit belegen.
$$
	\begin{description}
		\item[\(\bm{D(v)\leq \delta(v)}\)] Der Beweis erfolgt per Induktion über die Pfadlänge eines kürzesten Pfades.
		\begin{description}
			\item[Induktionsanfang] Ein Pfad der Länge eins, besteht nur aus dem Startknoten $s$ selbst. Dieser ist auch der eindeutige kürzeste Pfad, da aufgrund der positiven Kantengewichte alle längeren Pfade positive Kosten haben. Daraus und der Starteigenschaft folgt, dass $D(s)=\delta(s)=0$.
			\item[Induktionsschritt] Wir haben einen kürzesten Pfad $(v_1,\ldots,v_{i+1})$ der Länge $i+1$. Wir nehmen an, dass für Pfade der Länge $i$ gilt, dass $D(v_i)\leq \delta(v_i)$. Weiterhin gilt wegen der optimalen Substruktur von kürzesten Pfaden, dass $\delta(v_{i+1})=\delta(v_i)+c(\{v_i,v_{i+1}\})$.
			\begin{align*}
				D(v_{i+1}) & \leq D(v_i) + c(\{v_i,v_{i+1}\})       & \text{(Dreiecksungleichung)}  \\
				           & \leq \delta(v_i) + c(\{v_i, v_{i+1}\}) & \text{(Induktionsannahme)}    \\
				           & = \delta(v_i+1)                        & \text{(optimale Substruktur)} 
			\end{align*}
		\end{description}
		\item[$\bm{D(v)\geq \delta(v)}$] Zur Erzeugen eines Widerspruchs nehmen wir an, dass es ein $v$ gibt, sodass $D(v)<\delta(v)$. Von allen $v$ mit $D(v)<\delta(v)$, sei $v$ so gewählt, dass $D(v)$ minimal ist (das heißt für alle $v'$ mit $D(v') < D(v)$ ist $D(v')\geq\delta(v')$). Da $D(s)=\delta(s)=0$, wissen wir, dass $v\neq s$. Dann muss es wegen der Ausgleichseigenschaft, einen Knoten $u$ geben, sodass $D(v)=D(u)+c(\{u,v\})$.  Aufgrund der positiven Kantengewichte ist $D(u) < D(v)$. Wegen unser Wahl von $v$, muss $D(u)\geq \delta(u)$ sein. Aufgrund der ersten Richtung gilt aber auch $D(u)\leq \delta(u)$. Zusammen ist also $D(u)=\delta(u)$. Mit der Ausgleichskante, können wir einen Pfad nach $v$ mit Kosten $\delta(u)+c(\{u,v\})$ konstruieren. Ein kürzester Pfad nach $v$ hat Kosten $\delta(v)$. Deswegen muss $\delta(v) \leq \delta(u)+c(\{u,v\})$ sein. Zusammen gilt:
		\begin{align*}
			\delta(v) & \leq \delta(u) + c(\{u,v\}) &                        \\
			          & = D(u) + c(\{u,v\})         & (D(u)=\delta(u))       \\
			          & = D(v),                     & (D(v)=D(u)+c(\{u,v\})) 
		\end{align*}
		was ein Widerspruch zur Annahme darstellt.
	\end{description}
$$