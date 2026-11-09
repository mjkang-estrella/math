import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8654 : CNF.NClause := [(221,true),(222,true),(228,true),(234,false),(240,true),(243,true)]
theorem inputList8654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) inputClause8654 (by decide) v hb
mask_input "8654|27606985387162255149739023449108101809804435888681546220650096895197184|15902065052132133557976315179058316588899635880120489724968833883251408896"
def inputClause8658 : CNF.NClause := [(219,true),(222,true),(230,true),(233,true),(241,true),(245,false)]
theorem inputList8658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) inputClause8658 (by decide) v hb
mask_input "8658|56539106072908298546665520023773392506479484700019806659891398441363832832|3549230641322047563805765452273953563194109749385490125528338392479170560"
def inputClause8659 : CNF.NClause := [(219,true),(222,true),(230,true),(233,true),(241,false),(245,true)]
theorem inputList8659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) inputClause8659 (by decide) v hb
mask_input "8659|3533694129556768659166595001485837031654967793751237916243212402585239552|56554642584673577451304690474561509038018626655654058869176524431257763840"
def inputClause8660 : CNF.NClause := [(219,true),(222,true),(230,true),(233,false),(241,true),(245,true)]
theorem inputList8660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) inputClause8660 (by decide) v hb
mask_input "8660|13803492693581127574869511724554050904902217944340773110325048447598592|60074533221536764982896415964322792018768692231460956012309411785395404800"
def inputClause8661 : CNF.NClause := [(219,true),(222,true),(230,false),(233,true),(241,true),(245,true)]
theorem inputList8661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) inputClause8661 (by decide) v hb
mask_input "8661|1725436586697640946858688965569256363112777243042596638790631055949824|60086611277643648469524426787081776813310481672162254188780946202787053568"
def inputClause8663 : CNF.NClause := [(219,false),(222,true),(230,true),(233,true),(241,true),(245,true)]
theorem inputList8663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) inputClause8663 (by decide) v hb
mask_input "8663|842498333348457493583344221469363458551160763204392890034487820288|60088335871732012762013791892703124600310135898244533581026846799355183104"
def inputClause8670 : CNF.NClause := [(218,true),(222,true),(231,true),(235,true),(239,true),(246,false)]
theorem inputList8670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) inputClause8670 (by decide) v hb
mask_input "8670|113078212145816597093331040047546785012958969400039613319782796882727665664|942095537572745418873539633626696463848974059567745002119249849695076352"
def inputClause8671 : CNF.NClause := [(218,true),(222,true),(231,true),(235,true),(239,false),(246,true)]
theorem inputList8671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) inputClause8671 (by decide) v hb
mask_input "8671|883423532389192164791648750371459257913741948437809479060803100646309888|113136884151000150347412930930802022218894201511169548842841243631776432128"
def inputClause8672 : CNF.NClause := [(218,true),(222,true),(231,true),(235,false),(239,true),(246,true)]
theorem inputList8672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) inputClause8672 (by decide) v hb
mask_input "8672|55213970774324510299478046898216203619608871777363092441300193790394368|113965093712615018001905101634275265273188334587829995229460746538632347648"
def inputClause8673 : CNF.NClause := [(218,true),(222,true),(231,false),(235,true),(239,true),(246,true)]
theorem inputList8673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) inputClause8673 (by decide) v hb
mask_input "8673|3450873173395281893717377931138512726225554486085193277581262111899648|114016856810215947230310862303242342964081717905121273128624465470310842368"
def inputClause8694 : CNF.NClause := [(217,true),(225,true),(228,true),(236,true),(239,true),(245,false)]
theorem inputList8694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) inputClause8694 (by decide) v hb
mask_input "8694|56539106072908298546665520023773392506479484700019806659891398441363832832|994336963602433234021282246275513385845949798382332195346285861833539584"
def inputClause8695 : CNF.NClause := [(217,true),(225,true),(228,true),(236,true),(239,false),(245,true)]
theorem inputList8695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) inputClause8695 (by decide) v hb
mask_input "8695|883423532389192164791648750371459257913741948437809479060803100646309888|56650019504121539615895153519677446634411692549964329376176881202551062528"
def inputClause8696 : CNF.NClause := [(217,true),(225,true),(228,true),(236,false),(239,true),(245,true)]
theorem inputList8696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) inputClause8696 (by decide) v hb
mask_input "8696|110427941548649020598956093796432407239217743554726184882600387580788736|57423015094962082760087846176252473485086216754847412670355083915616583680"
def inputClause8697 : CNF.NClause := [(217,true),(225,true),(228,false),(236,true),(239,true),(245,true)]
theorem inputList8697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) inputClause8697 (by decide) v hb
mask_input "8697|431359146674410236714672241392314090778194310760649159697657763987456|57533011677364057370450087597807513578234656304091378206077986645433384960"
def inputClause8707 : CNF.NClause := [(217,true),(222,true),(227,true),(232,true),(237,false),(242,true)]
theorem inputList8707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) inputClause8707 (by decide) v hb
mask_input "8707|220855883097298041197912187592864814478435487109452369765200775161577472|7074512635644915212013304157544474368056308840706322979862778942800789504"
def inputClause8708 : CNF.NClause := [(217,true),(222,true),(227,true),(232,false),(237,true),(242,true)]
theorem inputList8708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) inputClause8708 (by decide) v hb
mask_input "8708|6901746346790563787434755862277025452451108972170386555162524223799296|7288466772395422689423781589275062157082293218843604963072817193738567680"
def inputClause8713 : CNF.NClause := [(273,true),(274,true),(275,true),(276,true),(277,false),(278,true)]
theorem inputList8713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) inputClause8713 (by decide) v hb
mask_input "8713|242833611528216133864932738352939863330300854881517440156476551217363035650651062272|713323733864134893228239918911760848532758761214457480459649869201003917223787495424"
def inputClause8714 : CNF.NClause := [(273,true),(274,true),(275,true),(276,false),(277,true),(278,true)]
theorem inputList8714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) inputClause8714 (by decide) v hb
mask_input "8714|121416805764108066932466369176469931665150427440758720078238275608681517825325531136|834740539628242960160706288088230780197909188655216200537888144809685435049113026560"
def inputClause8715 : CNF.NClause := [(273,true),(274,true),(275,false),(276,true),(277,true),(278,true)]
theorem inputList8715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) inputClause8715 (by decide) v hb
mask_input "8715|60708402882054033466233184588234965832575213720379360039119137804340758912662765568|895448942510296993626939472676465746030484402375595560577007282614026193961775792128"
def inputClause8716 : CNF.NClause := [(273,true),(274,false),(275,true),(276,true),(277,true),(278,true)]
theorem inputList8716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) inputClause8716 (by decide) v hb
mask_input "8716|30354201441027016733116592294117482916287606860189680019559568902170379456331382784|925803143951324010360056064970583228946772009235785240596566851516196573418107174912"
def inputClause8723 : CNF.NClause := [(252,false),(257,true),(262,true),(267,true),(272,true),(273,true)]
theorem inputList8723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 1) (closed_mem 4 1) inputClause8723 (by decide) v hb
mask_input "8723|7237005577332262213973186563042994240829374041602535252466099000494570602496|23010435557417948986962873282896478424417517892725424167049090009220512948307361792"
def inputClause8725 : CNF.NClause := [(250,true),(255,true),(260,true),(265,true),(270,false),(273,true)]
theorem inputList8725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) inputClause8725 (by decide) v hb
mask_input "8725|1897137590064188545819787018382342682267975428761855001222473056385648716020711424|15238298648926824308905206905932473778192816824334141448508450900758121940823048192"
def inputClause8726 : CNF.NClause := [(250,true),(255,true),(260,true),(265,false),(270,true),(273,true)]
theorem inputList8726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) inputClause8726 (by decide) v hb
mask_input "8726|59285549689505892056868344324448208820874232148807968788202283012051522375647232|17076150689301506962668125579990368251639918020947188480942721674131719134468112384"
def inputClause8727 : CNF.NClause := [(250,true),(255,true),(260,false),(265,true),(270,true),(273,true)]
theorem inputList8727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) inputClause8727 (by decide) v hb
mask_input "8727|1852673427797059126777135760139006525652319754650249024631321344126610074238976|17133583565563215795598216788554677453935139933341346200706292635799644046769520640"
def inputClause8728 : CNF.NClause := [(250,true),(255,false),(260,true),(265,true),(270,true),(273,true)]
theorem inputList8728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) inputClause8728 (by decide) v hb
mask_input "8728|57896044618658097711785492504343953926634992332820282019728792003956564819968|17135378342946394196627282138822312116506865618103663629448904228351766700278939648"
def inputClause8729 : CNF.NClause := [(250,false),(255,true),(260,true),(265,true),(270,true),(273,true)]
theorem inputList8729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) inputClause8729 (by decide) v hb
mask_input "8729|1809251394333065553493296640760748560207343510400633813116524750123642650624|17135434429739618521659440431018175699712232045752486049097110840619020533201108992"
def inputClause8731 : CNF.NClause := [(251,true),(256,true),(261,true),(266,true),(271,false),(273,true)]
theorem inputList8731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) inputClause8731 (by decide) v hb
mask_input "8731|3794275180128377091639574036764685364535950857523710002444946112771297432041422848|15299496577340140251252117664806206098241830218573442887237117350431054153480404992"
def inputClause8733 : CNF.NClause := [(251,true),(256,true),(261,false),(266,true),(271,true),(273,true)]
theorem inputList8733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) inputClause8733 (by decide) v hb
mask_input "8733|3705346855594118253554271520278013051304639509300498049262642688253220148477952|19090066410612923224638137430050613449726476436587852391632800820514098365373349888"
def inputClause8734 : CNF.NClause := [(251,true),(256,false),(261,true),(266,true),(271,true),(273,true)]
theorem inputList8734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) inputClause8734 (by decide) v hb
mask_input "8734|115792089237316195423570985008687907853269984665640564039457584007913129639936|19093655965379280026696268130585882774869927806112487249118024005618343672392187904"
def inputClause8735 : CNF.NClause := [(251,false),(256,true),(261,true),(266,true),(271,true),(273,true)]
theorem inputList8735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) inputClause8735 (by decide) v hb
mask_input "8735|3618502788666131106986593281521497120414687020801267626233049500247285301248|19093768138965728676760584714977609941280660661410132088414437230152851338236526592"
def inputClause8737 : CNF.NClause := [(249,true),(254,true),(259,true),(264,true),(269,false),(273,true)]
theorem inputList8737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) inputClause8737 (by decide) v hb
mask_input "8737|948568795032094272909893509191171341133987714380927500611236528192824358010355712|15207699684720166337731751526495607618168310127214490729144117675921655834494369792"
def inputClause8738 : CNF.NClause := [(249,true),(254,true),(259,true),(264,false),(269,true),(273,true)]
theorem inputList8738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) inputClause8738 (by decide) v hb
mask_input "8738|29642774844752946028434172162224104410437116074403984394101141506025761187823616|16126625704907507664613210863524554854891860725521014245361253062608454431316901888"
def inputClause8739 : CNF.NClause := [(249,true),(254,true),(259,false),(264,true),(269,true),(273,true)]
theorem inputList8739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) inputClause8739 (by decide) v hb
mask_input "8739|926336713898529563388567880069503262826159877325124512315660672063305037119488|16155342143038362081078256467806709456039471681718093105243038543442416887467606016"
def inputClause8740 : CNF.NClause := [(249,true),(254,false),(259,true),(264,true),(269,true),(273,true)]
theorem inputList8740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) inputClause8740 (by decide) v hb
mask_input "8740|28948022309329048855892746252171976963317496166410141009864396001978282409984|16156239531729951281592789142940526787325334524099251819614344339718478214222315520"
def inputClause8741 : CNF.NClause := [(249,false),(254,true),(259,true),(264,true),(269,true),(273,true)]
theorem inputList8741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) inputClause8741 (by decide) v hb
mask_input "8741|904625697166532776746648320380374280103671755200316906558262375061821325312|16156267575126563444108868289038458578928017737923663029438447645852105130683400192"
def inputClause8743 : CNF.NClause := [(268,true),(269,true),(270,true),(271,true),(272,false),(278,true)]
theorem inputList8743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) inputClause8743 (by decide) v hb
mask_input "8743|7588550360256754183279148073529370729071901715047420004889892225542594864082845696|492781489019172974776689678024813511719106617620891836567537376396172253986379792384"
def inputClause8744 : CNF.NClause := [(268,true),(269,true),(270,true),(271,false),(272,true),(278,true)]
theorem inputList8744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) inputClause8744 (by decide) v hb
mask_input "8744|3794275180128377091639574036764685364535950857523710002444946112771297432041422848|496575764199301351868329252061578197083642568478415546569982322508943551418421215232"
def inputClause8746 : CNF.NClause := [(268,true),(269,false),(270,true),(271,true),(272,true),(278,true)]
theorem inputList8746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) inputClause8746 (by decide) v hb
mask_input "8746|948568795032094272909893509191171341133987714380927500611236528192824358010355712|499421470584397634687058932589151711107044531621558329071816032093522024492452282368"
def inputClause8747 : CNF.NClause := [(268,false),(269,true),(270,true),(271,true),(272,true),(278,true)]
theorem inputList8747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) inputClause8747 (by decide) v hb
mask_input "8747|474284397516047136454946754595585670566993857190463750305618264096412179005177856|499895754981913681823513879343747296777611525478748792822121650357618436671457460224"
def inputClause8753 : CNF.NClause := [(252,false),(256,true),(260,true),(264,true),(268,true),(277,true)]
theorem inputList8753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 6) (closed_mem 4 6) inputClause8753 (by decide) v hb
mask_input "8753|7237005577332262213973186563042994240829374041602535252466099000494570602496|243339507166093968322738319986442820799711791444521623780764941401893608114047942656"
end Percolation.MaskChain
