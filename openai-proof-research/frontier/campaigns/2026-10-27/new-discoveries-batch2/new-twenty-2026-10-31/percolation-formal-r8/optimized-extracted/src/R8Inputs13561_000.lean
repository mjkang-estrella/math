import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause568 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,false),(20,true),(28,true)]
theorem inputList568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause568 (by decide) v hb
mask_input "568|1180591620717411434496|269500488"
def inputClause7950 : CNF.NClause := [(44,false),(96,false),(102,false),(103,false),(109,false),(115,false),(119,false)]
theorem inputList7950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 13) (final_mem 13) inputClause7950 (by decide) v hb
mask_input "7950|706816700903418663950886958983544832|0"
def inputClause8041 : CNF.NClause := [(126,true),(130,true),(134,true),(143,true),(147,false),(153,true)]
theorem inputList8041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) inputClause8041 (by decide) v hb
mask_input "8041|178405961588244985132285746181186892047843328|11429155138518486714087186990049242489995395072"
def inputClause8042 : CNF.NClause := [(126,true),(130,true),(134,true),(143,false),(147,true),(153,true)]
theorem inputList8042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) inputClause8042 (by decide) v hb
mask_input "8042|11150372599265311570767859136324180752990208|11596410727507466387648704877094105201290248192"
def inputClause8051 : CNF.NClause := [(127,false),(133,true),(134,true),(140,true),(146,true),(150,true)]
theorem inputList8051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) inputClause8051 (by decide) v hb
mask_input "8051|170141183460469231731687303715884105728|1517877137182214947663267308894442554749091840"
def inputClause8052 : CNF.NClause := [(125,true),(132,true),(134,true),(141,true),(148,true),(151,false)]
theorem inputList8052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) inputClause8052 (by decide) v hb
mask_input "8052|2854495385411919762116571938898990272765493248|359626781450955838351648460036875299711877120"
def inputClause8065 : CNF.NClause := [(128,true),(130,true),(137,true),(139,true),(146,false),(151,true)]
theorem inputList8065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) inputClause8065 (by decide) v hb
mask_input "8065|89202980794122492566142873090593446023921664|2855368209683071969275355494767052758227877888"
def inputClause8066 : CNF.NClause := [(128,true),(130,true),(137,true),(139,false),(146,true),(151,true)]
theorem inputList8066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) inputClause8066 (by decide) v hb
mask_input "8066|696898287454081973172991196020261297061888|2943874292189740379868325376661625942954737664"
def inputClause8081 : CNF.NClause := [(127,false),(131,true),(135,true),(139,true),(148,true),(153,true)]
theorem inputList8081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) inputClause8081 (by decide) v hb
mask_input "8081|170141183460469231731687303715884105728|11775536641513524348335063258100965856931479552"
def inputClause8083 : CNF.NClause := [(125,true),(133,true),(136,true),(139,true),(147,false),(152,true)]
theorem inputList8083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) inputClause8083 (by decide) v hb
mask_input "8083|178405961588244985132285746181186892047843328|5709785712968262701601102253802767085043974144"
def inputClause8094 : CNF.NClause := [(128,true),(129,true),(135,true),(141,true),(147,true),(150,false)]
theorem inputList8094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) inputClause8094 (by decide) v hb
mask_input "8094|1427247692705959881058285969449495136382746624|181238131728127955963691413038841498871791616"
def inputClause8101 : CNF.NClause := [(126,true),(129,true),(137,true),(140,true),(148,false),(152,true)]
theorem inputList8101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) inputClause8101 (by decide) v hb
mask_input "8101|356811923176489970264571492362373784095686656|5710559557605936780784325900581892854927851520"
def inputClause8114 : CNF.NClause := [(125,true),(129,true),(138,true),(142,false),(146,true),(153,true)]
theorem inputList8114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) inputClause8114 (by decide) v hb
mask_input "8114|5575186299632655785383929568162090376495104|11507533694685558289013251983955605460241874944"
def inputClause8117 : CNF.NClause := [(125,false),(129,true),(138,true),(142,true),(146,true),(153,true)]
theorem inputList8117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) inputClause8117 (by decide) v hb
mask_input "8117|42535295865117307932921825928971026432|11513108838449895079681327980601941621647343616"
def inputClause8537 : CNF.NClause := [(221,false),(226,true),(231,true),(236,true),(241,true),(242,true)]
theorem inputList8537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) inputClause8537 (by decide) v hb
mask_input "8537|3369993333393829974333376885877453834204643052817571560137951281152|10715069043179018882551637144245430093453041227872215289179743271889403904"
def inputClause8580 : CNF.NClause := [(218,true),(224,true),(230,true),(236,true),(237,true),(243,false)]
theorem inputList8580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) inputClause8580 (by decide) v hb
mask_input "8580|14134776518227074636666380005943348126619871175004951664972849610340958208|333036642428478527612268429042064232393168920632025294055517914652475392"
def inputClause8640 : CNF.NClause := [(218,true),(226,true),(229,true),(232,true),(240,true),(245,false)]
theorem inputList8640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) inputClause8640 (by decide) v hb
mask_input "8640|56539106072908298546665520023773392506479484700019806659891398441363832832|1774719790454358990632087060820438982665915218627382407482533472729300992"
def inputClause8655 : CNF.NClause := [(221,true),(222,true),(228,false),(234,true),(240,true),(243,true)]
theorem inputList8655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) inputClause8655 (by decide) v hb
mask_input "8655|431359146674410236714672241392314090778194310760649159697657763987456|15929240678372621402889339530266032376618662121698410622029786322382618624"
def inputClause8674 : CNF.NClause := [(218,true),(222,false),(231,true),(235,true),(239,true),(246,true)]
theorem inputList8674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) inputClause8674 (by decide) v hb
mask_input "8674|6739986666787659948666753771754907668409286105635143120275902562304|114020300943402675724544631014419709721900275050321252686758926456520179712"
def inputClause8682 : CNF.NClause := [(217,true),(226,true),(230,true),(234,true),(238,true),(246,false)]
theorem inputList8682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) inputClause8682 (by decide) v hb
mask_input "8682|113078212145816597093331040047546785012958969400039613319782796882727665664|471152238579707918165974151496810432993347373718509845777989201337253888"
def inputClause8685 : CNF.NClause := [(217,true),(226,true),(230,false),(234,true),(238,true),(246,true)]
theorem inputList8685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) inputClause8685 (by decide) v hb
mask_input "8685|1725436586697640946858688965569256363112777243042596638790631055949824|113547638947809607370550155510078026189589203996515080568921995453008969728"
def inputClause8690 : CNF.NClause := [(217,true),(224,true),(231,true),(233,false),(240,true),(244,true)]
theorem inputList8690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) inputClause8690 (by decide) v hb
mask_input "8690|13803492693581127574869511724554050904902217944340773110325048447598592|30039878144977179372563942953411895668764990076306220823015590296318640128"
def inputClause9091 : CNF.NClause := [(314,true),(319,true),(324,true),(329,true),(334,false),(335,true)]
theorem inputList9091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) inputClause9091 (by decide) v hb
mask_input "9091|34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184|71120925716338018822685877661688650883120741795906450777241201317377661321638313396348151236466311168"
def inputClause9093 : CNF.NClause := [(314,true),(319,true),(324,false),(329,true),(334,true),(335,true)]
theorem inputList9093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) inputClause9093 (by decide) v hb
mask_input "9093|34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216|106082761520291475051327592948271879894937809417840143315734378354211753793215837919123994675444187136"
def inputClause9095 : CNF.NClause := [(314,false),(319,true),(324,true),(329,true),(334,true),(335,true)]
theorem inputList9095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) inputClause9095 (by decide) v hb
mask_input "9095|33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384|106116903938068773348425875873356433829519662022939687937354000597411787086645112845415767960052563968"
def inputClause9098 : CNF.NClause := [(312,true),(317,true),(322,true),(327,false),(332,true),(335,true)]
theorem inputList9098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) inputClause9098 (by decide) v hb
mask_input "9098|273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728|78749845382410962097554968996325858279999783335124909359678655983021855183092182208942467618634203136"
def inputClause9117 : CNF.NClause := [(330,true),(331,true),(332,false),(333,true),(334,true),(340,true)]
theorem inputList9117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) inputClause9117 (by decide) v hb
mask_input "9117|8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296|2298800511746945532515499840700620054986181071868766270683484907336860602158544095307912349051229569024"
def inputClause9140 : CNF.NClause := [(311,true),(317,true),(323,true),(329,false),(330,true),(336,true)]
theorem inputList9140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) inputClause9140 (by decide) v hb
mask_input "9140|1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912|142188656177412312011659608991784786221293633815710226399268350432526140761004304629310867337052684288"
def inputClause9148 : CNF.NClause := [(320,true),(321,false),(322,true),(323,true),(324,true),(340,true)]
theorem inputList9148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) inputClause9148 (by decide) v hb
mask_input "9148|4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152|2239806685801845916949831736197923195132968975665797877830317565170418715552208583956828159172128276480"
def inputClause9149 : CNF.NClause := [(320,false),(321,true),(322,true),(323,true),(324,true),(340,true)]
theorem inputList9149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) inputClause9149 (by decide) v hb
mask_input "9149|2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576|2239808821788881837859914131219629364685083578370320234483087512212026537771934364597378182134215213056"
def inputClause9176 : CNF.NClause := [(325,true),(326,true),(327,true),(328,false),(329,true),(340,true)]
theorem inputList9176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) inputClause9176 (by decide) v hb
mask_input "9176|546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456|2241316828636242000378085016544185068477993087763104031338670123587149024898335496825694393367592435712"
def inputClause9190 : CNF.NClause := [(312,true),(318,false),(324,true),(325,true),(331,true),(336,true)]
theorem inputList9190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) inputClause9190 (by decide) v hb
mask_input "9190|533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144|144461083557102349758595117387212688339623059922839680592733200625863645049542085509780120390890160128"
def inputClause9192 : CNF.NClause := [(313,true),(317,true),(321,true),(325,true),(334,true),(339,false)]
theorem inputList9192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) inputClause9192 (by decide) v hb
mask_input "9192|1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888|35068918841527709978631784460712057261187423519745900669936537708688742346423886791600041467976876032"
def inputClause9194 : CNF.NClause := [(313,true),(317,true),(321,true),(325,false),(334,true),(339,true)]
theorem inputList9194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) inputClause9194 (by decide) v hb
mask_input "9194|68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432|1154872938345280346134716284050336770654342885592355255231292782859134366905279378984438053316998463488"
def inputClause9231 : CNF.NClause := [(311,true),(315,true),(324,false),(328,true),(332,true),(339,true)]
theorem inputList9231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) inputClause9231 (by decide) v hb
mask_input "9231|34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216|1129168257590674458018771854271677117524483773866544514178040577707004120558817152924469440119314579456"
def inputClause9237 : CNF.NClause := [(310,true),(311,true),(312,false),(313,true),(314,true),(340,true)]
theorem inputList9237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) inputClause9237 (by decide) v hb
mask_input "9237|8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096|2239744798497774884253313593718430671264132893985647682975794558551803014930095121237610745830177767424"
def inputClause9240 : CNF.NClause := [(310,true),(319,true),(323,true),(327,true),(331,true),(339,false)]
theorem inputList9240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) inputClause9240 (by decide) v hb
mask_input "9240|1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888|4666065765894067841505677256015771525552844945791743089868033043695459129854260239181947810711863296"
def inputClause9241 : CNF.NClause := [(310,true),(319,true),(323,true),(327,true),(331,false),(339,true)]
theorem inputList9241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) inputClause9241 (by decide) v hb
mask_input "9241|4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648|1120163935405230149271481813086002667855669254701330085667011042312771488721535981083173668092469313536"
def inputClause9243 : CNF.NClause := [(310,true),(319,true),(323,false),(327,true),(331,true),(339,true)]
theorem inputList9243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) inputClause9243 (by decide) v hb
mask_input "9243|17087896287367280659160173649356416916821636178853222159576332862577757806245124400183696695492608|1124521348958508805839567657366588554169458771926937657317703007192728816962128487805220510749819928576"
def inputClause9255 : CNF.NClause := [(310,true),(318,true),(321,false),(329,true),(332,true),(338,true)]
theorem inputList9255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) inputClause9255 (by decide) v hb
mask_input "9255|4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152|569779349888658426293071181258455292993732524340516063966024450381602531985255324117519475486826168320"
end Percolation.MaskChain
