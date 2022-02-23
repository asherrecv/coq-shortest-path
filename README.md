# Definitionen

Sei <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/7a08e056acdb1b01acdf8fd01d2e4d5d.svg?invert_in_darkmode" align=middle width=93.52942664999999pt height=24.65753399999998pt/> ein ungerichteter, zusammenhängender Graph mit einem ausgezeichneten Startknoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/77f8613a336072e8b46b3ed88c5bce3b.svg?invert_in_darkmode" align=middle width=41.03865479999999pt height=22.465723500000017pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/79dcf0afb251bc2970e7cb7d3146afdf.svg?invert_in_darkmode" align=middle width=88.1637504pt height=22.648391699999998pt/> eine Kantenbewertungsfunktion.

_Definition_ (__Pfad__) Ein Pfad <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/2ec6e630f199f589a2402fdf3e0289d5.svg?invert_in_darkmode" align=middle width=8.270567249999992pt height=14.15524440000002pt/> von einem Knoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/77f8613a336072e8b46b3ed88c5bce3b.svg?invert_in_darkmode" align=middle width=41.03865479999999pt height=22.465723500000017pt/> zu einem Knoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/0fc9dd50fcdde583fb41ba32a5024ca3.svg?invert_in_darkmode" align=middle width=39.26927234999999pt height=22.465723500000017pt/> ist eine Folge von Knoten <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/25cd1ce58c1c573212c742783b2c97de.svg?invert_in_darkmode" align=middle width=81.57337979999998pt height=24.65753399999998pt/>, so dass <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/1f8ea1cdde2fee4caeb137342d2e9cc8.svg?invert_in_darkmode" align=middle width=44.96563664999999pt height=14.15524440000002pt/>, <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/c4a0f2d804c46cde69566dad19e1c71f.svg?invert_in_darkmode" align=middle width=44.769732149999996pt height=20.221802699999984pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/0b541cf0a2348f821413e72b287a7e0b.svg?invert_in_darkmode" align=middle width=100.44327314999998pt height=24.65753399999998pt/> für alle <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/70d77aca7f3760e378d91a6e87c89fc6.svg?invert_in_darkmode" align=middle width=95.89497389999998pt height=21.68300969999999pt/>.

_Definition_ (__Pfadkosten__) Die Pfadkosten eines Pfades <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/57a792b026c4a8d081bb5d435f31ba25.svg?invert_in_darkmode" align=middle width=111.76157684999998pt height=24.65753399999998pt/> entsprechen der Summe der Kantengewichte entlang des Pfades, also dem Wert <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/06b466f234e2dbdcb73da1ba5dc4b276.svg?invert_in_darkmode" align=middle width=167.52603779999998pt height=24.657735299999988pt/>.

_Definition_ (__Kürzeste-Wege-Funktion__) Eine Funktion <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/57e23ebab792a071e2b0a6efb18ecfcc.svg?invert_in_darkmode" align=middle width=89.13787079999999pt height=22.831056599999986pt/> heißt Kürzeste-Wege-Funktion des Graphen <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/5201385589993766eea584cd3aa6fa13.svg?invert_in_darkmode" align=middle width=12.92464304999999pt height=22.465723500000017pt/>, wenn <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/8efbc740f360e04d0f6c920b8b4de6d9.svg?invert_in_darkmode" align=middle width=377.23579244999996pt height=24.65753399999998pt/> für alle <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/a3e83e340d51acde28b44ffd6bc6fbca.svg?invert_in_darkmode" align=middle width=41.89101674999999pt height=22.465723500000017pt/>,

# Überprüfung einer Kürzesten-Wege-Funktion

Ein Algorithmus zur Lösung des Kürzesten-Pfade-Problems mit einer Quelle, wie beispielsweise der Dijkstra-Algorithmus, berechnet einen Spannbaum mit der Quelle als Wurzel. Der Weg von der Wurzel zu einem Knoten des Spannbaums, hat minimale Pfadkosten. Der Spannbaum ist nicht notwendigerweise eindeutig. Aus dem Spannbaum lässt sich jedoch eine eindeutige Funktion <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/e6487508e51e0bed72a8f920e2cbc39a.svg?invert_in_darkmode" align=middle width=95.27603084999998pt height=22.648391699999998pt/> ableiten. Die Funktionswerte entsprechen den Pfadkosten eines kürzesten Pfades. Wir beschränken uns zunächst darauf, wie diese Funktion auf ihre Korrektheit überprüft werden kann. 

# Zeugeneigenschaft

Eine Funktion <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/e6487508e51e0bed72a8f920e2cbc39a.svg?invert_in_darkmode" align=middle width=95.27603084999998pt height=22.648391699999998pt/> kann einfach darauf überprüft werden, ob sie eine Kürzeste-Wege-Funktion für den Graph <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/5201385589993766eea584cd3aa6fa13.svg?invert_in_darkmode" align=middle width=12.92464304999999pt height=22.465723500000017pt/> ist. Dafür ist es hinreichend, <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/78ec2b7008296ce0561cf83393cb746d.svg?invert_in_darkmode" align=middle width=14.06623184999999pt height=22.465723500000017pt/> auf drei Eigenschaften zu überprüfen. 
Das heißt es bedarf zur Überprüfung der Ergebniskorrektheit, keines zusätzlichen mathematisches Artefakts, welches als Zeuge fungiert -- die Ausgabe zertifiziert sich gewissermaßen selbst.

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/45675d9ca7c044494d656b43c2739d63.svg?invert_in_darkmode" align=middle width=616.9850643pt height=65.753424pt/></p>


Dann ist für alle <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/a3e83e340d51acde28b44ffd6bc6fbca.svg?invert_in_darkmode" align=middle width=41.89101674999999pt height=22.465723500000017pt/>

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/7027e7cb3f2af0f7f87e73f3852c5d0e.svg?invert_in_darkmode" align=middle width=91.1647077pt height=16.438356pt/></p>


Wir zeigen zwei Richtungen, die zusammen die Gleichheit belegen.

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/1378da8be642e842fdc565c26a522609.svg?invert_in_darkmode" align=middle width=675.6150686999999pt height=577.7168991pt/></p>

Gemäß dem lokalen Ansatz, erfolgt die Überprüfung des verteilten Ergebnisses mithilfe lokal berechneter Zeugen durch lokale Checker. Wie kann das Ergebnis des verteilten Bellman-Ford-Algorithmus auf Korrektheit überprüft werden? Wir beobachten, dass zur Feststellung der Gültigkeit der Dreiecksungleichung und der Ausgleichseigenschaft, ausschließlich die Funktionswerte der Nachbarschaft benötigt werden. Die Feststellung der Starteigenschaft benötigt keine zusätzliche Information. Dies motiviert die Definition des lokalen Zeugen einer Komponente, als die Menge der berechneten Werte der Nachtbarschaft. Dieser wird vom  lokale Checker zur Teilüberprüfung des globalen Ergebnisses verwendet. Beispielsweise hält nach der Ausführung des zertifizierenden verteilten Bellman"=Ford"=Algorithmus auf dem Netzwerk aus Abbildung, die Komponente <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/8cd34385ed61aca950a6b06d09fb50ac.svg?invert_in_darkmode" align=middle width=7.654137149999991pt height=14.15524440000002pt/> die Werte <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/59281f8ff2f0f56d90d71d25f19ee57f.svg?invert_in_darkmode" align=middle width=13.840267649999989pt height=14.15524440000002pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/527e1e22ae543d45a6aa56cd366988bc.svg?invert_in_darkmode" align=middle width=13.93408334999999pt height=14.15524440000002pt/> als lokalen Zeugen. Der Checker der Komponente <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/8cd34385ed61aca950a6b06d09fb50ac.svg?invert_in_darkmode" align=middle width=7.654137149999991pt height=14.15524440000002pt/> muss überprüfen, ob die Dreiecksungleichung und Ausgleichseigenschaft in der Nachbarschaft erfüllt sind. Die Überprüfung der Starteigenschaft entfällt, da <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/8cd34385ed61aca950a6b06d09fb50ac.svg?invert_in_darkmode" align=middle width=7.654137149999991pt height=14.15524440000002pt/> nicht die Quelle ist. Zur Überprüfung der Dreiecksungleichung müssen die Ungleichungen <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/a15bcd01f0a49b35ff1f1123e2a7e706.svg?invert_in_darkmode" align=middle width=80.61462254999999pt height=21.18721440000001pt/> und <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/5df1ca9b255339a2fcbf7552ac8393de.svg?invert_in_darkmode" align=middle width=80.70845804999999pt height=21.18721440000001pt/> überprüft werden. Weiterhin muss der lokale Checker zur Überprüfung der Ausgleichseigenschaft feststellen, ob eine der Ungleichung tatsächlich eine Gleichheit ist. Hier stellt er fest, dass <img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/d44a6286f677341f099d0071d41e9660.svg?invert_in_darkmode" align=middle width=80.70845804999999pt height=21.18721440000001pt/>.

<p align="center"><img src="https://raw.githubusercontent.com/asherrecv/coq-shortest-path/readme/svgs/41b97aceb3b80950427ad06e3ddd99db.svg?invert_in_darkmode" align=middle width=563.52766965pt height=145.30036619999998pt/></p>
