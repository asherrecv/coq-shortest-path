
Sei <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/7a08e056acdb1b01acdf8fd01d2e4d5d.svg?invert_in_darkmode" align=middle width=93.52942664999999pt height=24.65753399999998pt/> ein ungerichteter, zusammenhängender Graph mit einem ausgezeichneten Startknoten <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/77f8613a336072e8b46b3ed88c5bce3b.svg?invert_in_darkmode" align=middle width=41.03865479999999pt height=22.465723500000017pt/>. Weiterhin sei <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/79dcf0afb251bc2970e7cb7d3146afdf.svg?invert_in_darkmode" align=middle width=88.1637504pt height=22.648391699999998pt/> eine Kantenbewertungsfunktion. 


_Definition_ (__Pfad__) Ein Pfad <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/2ec6e630f199f589a2402fdf3e0289d5.svg?invert_in_darkmode" align=middle width=8.270567249999992pt height=14.15524440000002pt/> von einem Knoten <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/77f8613a336072e8b46b3ed88c5bce3b.svg?invert_in_darkmode" align=middle width=41.03865479999999pt height=22.465723500000017pt/> zu einem Knoten <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/0fc9dd50fcdde583fb41ba32a5024ca3.svg?invert_in_darkmode" align=middle width=39.26927234999999pt height=22.465723500000017pt/> ist eine Folge von Knoten <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/25cd1ce58c1c573212c742783b2c97de.svg?invert_in_darkmode" align=middle width=81.57337979999998pt height=24.65753399999998pt/>, so dass <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/1f8ea1cdde2fee4caeb137342d2e9cc8.svg?invert_in_darkmode" align=middle width=44.96563664999999pt height=14.15524440000002pt/>, <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/c4a0f2d804c46cde69566dad19e1c71f.svg?invert_in_darkmode" align=middle width=44.769732149999996pt height=20.221802699999984pt/> und <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/0b541cf0a2348f821413e72b287a7e0b.svg?invert_in_darkmode" align=middle width=100.44327314999998pt height=24.65753399999998pt/> für alle <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/70d77aca7f3760e378d91a6e87c89fc6.svg?invert_in_darkmode" align=middle width=95.89497389999998pt height=21.68300969999999pt/>.

_Definition_ (__Pfadkosten__) Die Pfadkosten eines Pfades <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/57a792b026c4a8d081bb5d435f31ba25.svg?invert_in_darkmode" align=middle width=111.76157684999998pt height=24.65753399999998pt/> entsprechen der Summe der Kantengewichte entlang des Pfades, also dem Wert <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/06b466f234e2dbdcb73da1ba5dc4b276.svg?invert_in_darkmode" align=middle width=167.52603779999998pt height=24.657735299999988pt/>.

_Definition_ (__Kürzeste-Wege-Funtion__) Eine Funktion <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/57e23ebab792a071e2b0a6efb18ecfcc.svg?invert_in_darkmode" align=middle width=89.13787079999999pt height=22.831056599999986pt/> heißt Kürzeste-Wege-Funktion des Graphen <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/5201385589993766eea584cd3aa6fa13.svg?invert_in_darkmode" align=middle width=12.92464304999999pt height=22.465723500000017pt/>, wenn <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/8efbc740f360e04d0f6c920b8b4de6d9.svg?invert_in_darkmode" align=middle width=377.23579244999996pt height=24.65753399999998pt/> für alle <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/a3e83e340d51acde28b44ffd6bc6fbca.svg?invert_in_darkmode" align=middle width=41.89101674999999pt height=22.465723500000017pt/>,

# Überprüfung einer Kürzesten-Wege-Funktion

Ein Algorithmus zur Lösung des Kürzesten-Pfade-Problems mit einer Quelle, wie beispielsweise der Dijkstra-Algorithmus, berechnet einen Spannbaum mit der Quelle als Wurzel. Der Weg von der Wurzel zu einem Knoten des Spannbaums, hat minimale Pfadkosten. Der Spannbaum ist nicht notwendigerweise eindeutig. Aus dem Spannbaum lässt sich jedoch eine eindeutige Funktion <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/e6487508e51e0bed72a8f920e2cbc39a.svg?invert_in_darkmode" align=middle width=95.27603084999998pt height=22.648391699999998pt/> ableiten. Die Funktionswerte entsprechen den Pfadkosten eines kürzesten Pfades. Wir beschränken uns zunächst darauf, wie diese Funktion auf ihre Korrektheit überprüft werden kann. 

# Zeugeneigenschaft

Eine Funktion <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/e6487508e51e0bed72a8f920e2cbc39a.svg?invert_in_darkmode" align=middle width=95.27603084999998pt height=22.648391699999998pt/> kann einfach darauf überprüft werden, ob sie tatsächlich identisch mit der Kürzeste-Wege-Funktion für den Graph <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/5201385589993766eea584cd3aa6fa13.svg?invert_in_darkmode" align=middle width=12.92464304999999pt height=22.465723500000017pt/> ist. Dazu muss die Ausgabe <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/78ec2b7008296ce0561cf83393cb746d.svg?invert_in_darkmode" align=middle width=14.06623184999999pt height=22.465723500000017pt/> lediglich auf drei Eigenschaften überprüft werden. In diesem Fall fällt der Zeuge mit der Ausgabe zusammen. Das heißt es bedarf zur Überprüfung der Ergebniskorrektheit, keines zusätzlichen mathematisches Artefakts, welches als Zeuge fungiert.

<p align="center"><img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/45675d9ca7c044494d656b43c2739d63.svg?invert_in_darkmode" align=middle width=616.9850643pt height=65.753424pt/></p>


Dann ist für alle <img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/a3e83e340d51acde28b44ffd6bc6fbca.svg?invert_in_darkmode" align=middle width=41.89101674999999pt height=22.465723500000017pt/>

<p align="center"><img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/7027e7cb3f2af0f7f87e73f3852c5d0e.svg?invert_in_darkmode" align=middle width=91.1647077pt height=16.438356pt/></p>


Wir zeigen zwei Richtungen, die zusammen die Gleichheit belegen.

<p align="center"><img src="https://rawgit.com/asherrecv/coq-shortest-path/None/svgs/1378da8be642e842fdc565c26a522609.svg?invert_in_darkmode" align=middle width=675.6150686999999pt height=577.7168991pt/></p>
