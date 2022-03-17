# Repository

## Formale Verifikation
Bei jedem Programm stellt sich die Frage, ob es tatsächlich für jede Eingabe korrekt gerechnet hat. Durch Tests lässt sich dies nicht erreichen, da nur endlich viele Eingaben überprüft werden. Ein:e Anwender:in könnte einer nicht getesteten Eingabe zum Opfer fallen. Eine sehr starke Korrektheitsgarantie erhält man durch formale Verifikation. Diese ist jeoch sehr aufwändig und oft sogar unmöglich. 

## Zertifizierende Algorithmen
Eine einfachere Möglichkeit ist, das Programm zusätzlich zur Ausgabe ein Zertifikat ausgeben zu lassen, welches auf die Ein- und Ausgabe zugeschnitten ist. Dieses sollte leicht überprüfbar sein und die Korrektheit der Programmausführung belegen. Die Überprüfung kann durch eine weitere Komponente - dem Checker automatisiert werden. Diesen Ansatz nennt man _zertifizierende Algorithmen_.

Beispielsweise ließe sich ein Programm, welches die Anzahl der Lösung einer quadratischen Gleichung im reellen Zahlenraum ausgibt, folgenderweise zertifizierend gestalten. Das Programm erwartet als Eingabe die Koeffizienten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/44bc9d542a92714cac84e01cbbb7fd61.svg?invert_in_darkmode" align=middle width=8.68915409999999pt height=14.15524440000002pt/>, <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/4bdc8d9bcfb35e1c9bfb51fc69687dfc.svg?invert_in_darkmode" align=middle width=7.054796099999991pt height=22.831056599999986pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/3e18a4a28fdee1744e5e3f79d13b9ff6.svg?invert_in_darkmode" align=middle width=7.11380504999999pt height=14.15524440000002pt/> einer quadratischen Gleichung. Neben der Anzahl der Lösungen (also keine, eine oder zwei) gibt das Programm zusätzlich auch die Diskriminante <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/cf576f48202482f07cecf3e4fa0da269.svg?invert_in_darkmode" align=middle width=58.542615449999985pt height=26.76175259999998pt/> aus. Die zusätzliche Ausgabe (die Diskriminante) dient als Zertifikat. Wenn ein:e Anwender:in grundlegendes Verständnis von mathematischen Zusammenhängen hat, versteht er:sie, was das Vorzeichen einer Diskriminante für die Programmausgabe (also der Anzahl der Lösungen) bedeutet. Außerdem ist es einach zu überprüfen, ob das Zertifikat zur Ein- und Ausgabe passt. Somit kann man sich anhand des Zertifkats einfach von der Korrektheit einer Berechnung überzeugen, ohne das Programm selbst verstehen zu müssen. Jedoch erhält man auch hier keine absolute Korrektheitsgarantie, da darauf vertraut werden muss, dass ein Zertifikat die korrekte Berechnung impliziert.

## Formale Instanzkorrektheit
Kombiniert man nun die formale Verifikation und die zertifizierenden Algorithmen, kommt man seinem Ziel der Korrektheitsgarantie ein ganzes Stückchen näher. 

 Zum einen lässt sich ein Checker formal verifizieren. Zum anderen lässt sich formal beweisen, dass das Zertifikat die korrekte Berechnung impliziert. Diese Implikation nennt man auch _Zeugeneigenschaft_. Die Korrektheit einer Berechnung ist damit -- bei Akzeptanz des Checkers -- durch einen maschinenüberprüfbaren Beweis abgesichert und so vertrauenswürdig, als wäre die Berechnung von einen formal verifizierten Algorithmus erfolgt. Das nennt man auch _formale Instanzkorrektheit_ [[2]](#2). Dadurch wird einer:em Anwender:in die Last genommen, die Eigenschaft selber vestehen zu müssen. Es muss lediglich dem formalen verifizierten Beweis der Zeugeneigenschaft vertraut werden.  

## Verteilte zertifizierende Algorithmen
Nun stellt sich die Frage, ob sich dieser Ansatz auch auf verteilte Algorithmen übertragen lässt. Für den verteilten Bellman-Ford-Algorithmus (und einige mehr) zur Berechnung kürzester Pfade in einem Netzwerk, lässt sich diese Frage bejahen [[3]](#3).  Die Idee bei der verteilten Berechnung ist, dass jede Komponente des Netzwerks ein lokales Zertifikat berechnet. Alle lokalen Zertifikate zusammen sollen die Korrektheit des verteilten Ergebnisses belegen (_verteilte Zeugeneigenschaft_). Die Überprüfung des verteilten Ergebnisses erfolgt ebenfalls verteilt durch lokale Checker, welche jeder Komponente zugewiesen werden. Das verteilte Ergebnis ist genau dann korrekt, wenn alle lokalen Checker das lokale Zertifikat akzeptieren. 

Dieses Repository enthält die Coq-Formalisierung der eben beschriebenen verteilten Zeugeneigenschaft zur verteilten Berechnung kürzester Pfade. Zunächst wird die Zeugeneigenschaft im klassischen Setting bewiesen und dann auf das verteilte Setting übertragen. 



# 1. Überprüfung einer Kürzesten-Wege-Funktion

Stellen wir uns vor, wir haben einen Graphen mit einem ausgezeichnet Startknoten und wollen die kürzeste Pfade zu allen anderen Knoten berechnen lassen. Das heißt wir suchen einen Kürzeste-Wege-Baum für den Graphen mit dem angegeben Startknoten. Das lässt sich zum Beispiel mit dem Algorithmus von Dijkstra lösen. Wie können wir den von Algorithmus ausgegeben Baum auf seine Korrektheit überprüfen? Welche Zeugeneigenschaft eignet sich hierfür? In diesem Abschnitt beschreiben wir, wie sich ein leicht abgewandelte Ausgabe zertifizieren lässt: Die Kürzeste-Wege-Funktion. Eine Kürzeste-Wege-Funktion und ein Kürzester-Wege-Baum lassen sich leicht ineinander umwandeln.

## 1.1. Definitionen

Sei <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/7a08e056acdb1b01acdf8fd01d2e4d5d.svg?invert_in_darkmode" align=middle width=93.52942664999999pt height=24.65753399999998pt/> ein ungerichteter, zusammenhängender Graph mit einem ausgezeichneten Startknoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/77f8613a336072e8b46b3ed88c5bce3b.svg?invert_in_darkmode" align=middle width=41.03865479999999pt height=22.465723500000017pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/79dcf0afb251bc2970e7cb7d3146afdf.svg?invert_in_darkmode" align=middle width=88.1637504pt height=22.648391699999998pt/> eine Kantenbewertungsfunktion.

_Definition_ (__Pfad__) Ein Pfad <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/2ec6e630f199f589a2402fdf3e0289d5.svg?invert_in_darkmode" align=middle width=8.270567249999992pt height=14.15524440000002pt/> von einem Knoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/77f8613a336072e8b46b3ed88c5bce3b.svg?invert_in_darkmode" align=middle width=41.03865479999999pt height=22.465723500000017pt/> zu einem Knoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/0fc9dd50fcdde583fb41ba32a5024ca3.svg?invert_in_darkmode" align=middle width=39.26927234999999pt height=22.465723500000017pt/> ist eine Folge von Knoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/25cd1ce58c1c573212c742783b2c97de.svg?invert_in_darkmode" align=middle width=81.57337979999998pt height=24.65753399999998pt/>, so dass <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/1f8ea1cdde2fee4caeb137342d2e9cc8.svg?invert_in_darkmode" align=middle width=44.96563664999999pt height=14.15524440000002pt/>, <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/c4a0f2d804c46cde69566dad19e1c71f.svg?invert_in_darkmode" align=middle width=44.769732149999996pt height=20.221802699999984pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/0b541cf0a2348f821413e72b287a7e0b.svg?invert_in_darkmode" align=middle width=100.44327314999998pt height=24.65753399999998pt/> für alle <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/70d77aca7f3760e378d91a6e87c89fc6.svg?invert_in_darkmode" align=middle width=95.89497389999998pt height=21.68300969999999pt/>.

_Definition_ (__Pfadkosten__) Die Pfadkosten eines Pfades <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/57a792b026c4a8d081bb5d435f31ba25.svg?invert_in_darkmode" align=middle width=111.76157684999998pt height=24.65753399999998pt/> entsprechen der Summe der Kantengewichte entlang des Pfades, also dem Wert <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/06b466f234e2dbdcb73da1ba5dc4b276.svg?invert_in_darkmode" align=middle width=167.52603779999998pt height=24.657735299999988pt/>.

_Definition_ (__Kürzeste-Wege-Funktion__) Eine Funktion <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/57e23ebab792a071e2b0a6efb18ecfcc.svg?invert_in_darkmode" align=middle width=89.13787079999999pt height=22.831056599999986pt/> heißt Kürzeste-Wege-Funktion des Graphen <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/5201385589993766eea584cd3aa6fa13.svg?invert_in_darkmode" align=middle width=12.92464304999999pt height=22.465723500000017pt/>, wenn <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/8efbc740f360e04d0f6c920b8b4de6d9.svg?invert_in_darkmode" align=middle width=377.23579244999996pt height=24.65753399999998pt/> für alle <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/a3e83e340d51acde28b44ffd6bc6fbca.svg?invert_in_darkmode" align=middle width=41.89101674999999pt height=22.465723500000017pt/>.


## 1.2. Zeugeneigenschaft

Eine Funktion <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/e6487508e51e0bed72a8f920e2cbc39a.svg?invert_in_darkmode" align=middle width=95.27603084999998pt height=22.648391699999998pt/> kann einfach darauf überprüft werden, ob sie eine Kürzeste-Wege-Funktion für den Graph <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/5201385589993766eea584cd3aa6fa13.svg?invert_in_darkmode" align=middle width=12.92464304999999pt height=22.465723500000017pt/> ist. Dafür ist es hinreichend, <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/78ec2b7008296ce0561cf83393cb746d.svg?invert_in_darkmode" align=middle width=14.06623184999999pt height=22.465723500000017pt/> auf drei Eigenschaften zu überprüfen. Das heißt es bedarf zur Überprüfung der Ergebniskorrektheit, keines zusätzlichen mathematisches Artefakts, welches als Zeuge fungiert -- die Ausgabe zertifiziert sich gewissermaßen selbst.

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/45675d9ca7c044494d656b43c2739d63.svg?invert_in_darkmode" align=middle width=616.9850643pt height=65.753424pt/></p>


Dann ist für alle <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/a3e83e340d51acde28b44ffd6bc6fbca.svg?invert_in_darkmode" align=middle width=41.89101674999999pt height=22.465723500000017pt/>

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/7027e7cb3f2af0f7f87e73f3852c5d0e.svg?invert_in_darkmode" align=middle width=91.1647077pt height=16.438356pt/></p>


Wir zeigen zwei Richtungen, die zusammen die Gleichheit belegen.

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/1378da8be642e842fdc565c26a522609.svg?invert_in_darkmode" align=middle width=675.6150686999999pt height=577.7168991pt/></p>


# 1.3. Verteilte Überprüfung eines Kürzesten-Wege-Netzwerks

Wie kann das Ergebnis des verteilten Bellman-Ford-Algorithmus auf Korrektheit überprüft werden? Wir beobachten, dass zur Feststellung der Gültigkeit der Dreiecksungleichung und der Ausgleichseigenschaft, ausschließlich die Funktionswerte der Nachbarschaft benötigt werden. Die Feststellung der Starteigenschaft benötigt keine zusätzliche Information. Dies motiviert die Definition des lokalen Zertifikat einer Komponente, als die Menge der berechneten Werte der Nachtbarschaft. Dieser wird vom lokalen Checker zur Teilüberprüfung des globalen Ergebnisses verwendet. Beispielsweise hält nach der Ausführung des zertifizierenden verteilten Bellman-Ford-Algorithmus auf dem Netzwerk aus Abbildung, die Komponente <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/8cd34385ed61aca950a6b06d09fb50ac.svg?invert_in_darkmode" align=middle width=7.654137149999991pt height=14.15524440000002pt/> die Werte <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/59281f8ff2f0f56d90d71d25f19ee57f.svg?invert_in_darkmode" align=middle width=13.840267649999989pt height=14.15524440000002pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/527e1e22ae543d45a6aa56cd366988bc.svg?invert_in_darkmode" align=middle width=13.93408334999999pt height=14.15524440000002pt/> als lokales Zertifikat. Der Checker der Komponente <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/8cd34385ed61aca950a6b06d09fb50ac.svg?invert_in_darkmode" align=middle width=7.654137149999991pt height=14.15524440000002pt/> muss überprüfen, ob die Dreiecksungleichung und Ausgleichseigenschaft in der Nachbarschaft erfüllt sind. Die Überprüfung der Starteigenschaft entfällt, da <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/8cd34385ed61aca950a6b06d09fb50ac.svg?invert_in_darkmode" align=middle width=7.654137149999991pt height=14.15524440000002pt/> nicht die Quelle ist. Zur Überprüfung der Dreiecksungleichung müssen die Ungleichungen <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/a15bcd01f0a49b35ff1f1123e2a7e706.svg?invert_in_darkmode" align=middle width=80.61462254999999pt height=21.18721440000001pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/5df1ca9b255339a2fcbf7552ac8393de.svg?invert_in_darkmode" align=middle width=80.70845804999999pt height=21.18721440000001pt/> überprüft werden. Weiterhin muss der lokale Checker zur Überprüfung der Ausgleichseigenschaft feststellen, ob eine der Ungleichung tatsächlich eine Gleichheit ist. Hier stellt er fest, dass <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/d44a6286f677341f099d0071d41e9660.svg?invert_in_darkmode" align=middle width=80.70845804999999pt height=21.18721440000001pt/>.

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/919ac95dfdac9aabc7fcc229ec5ae0ad.svg?invert_in_darkmode" align=middle width=563.52766965pt height=145.30036619999998pt/></p>

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

Definition einer Netzwerkcomponente mit eindeutigem Bezeichner <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/77a3b857d53fb44e33b53e4c8b68351a.svg?invert_in_darkmode" align=middle width=5.663225699999989pt height=21.68300969999999pt/>, der Nachbarschaftsmenge <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/97790d793f190b3b985b582fea9ceb20.svg?invert_in_darkmode" align=middle width=16.78561829999999pt height=22.465723500000017pt/> und der Information, ob die Komponente der Startknoten ist <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/master/svgs/55db458a5eab7d318df12f43aab09759.svg?invert_in_darkmode" align=middle width=19.573077149999992pt height=21.68300969999999pt/>.
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
