import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8401 : CNF.NClause := [(196,true),(197,true),(198,true),(199,true),(200,false),(216,true)]
theorem inputList8401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) inputClause8401 (by decide) v hb
mask_input "8401|1606938044258990275541962092341162602522202993782792835301376|105313798172973679501301348273132002158834959965855782622594072576"
def inputClause8403 : CNF.NClause := [(196,true),(197,true),(198,false),(199,true),(200,true),(216,true)]
theorem inputList8403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) inputClause8403 (by decide) v hb
mask_input "8403|401734511064747568885490523085290650630550748445698208825344|105315003376506873744008004744701258030786851618101119717220548608"
def inputClause8404 : CNF.NClause := [(196,true),(197,false),(198,true),(199,true),(200,true),(216,true)]
theorem inputList8404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) inputClause8404 (by decide) v hb
mask_input "8404|200867255532373784442745261542645325315275374222849104412672|105315204243762406117792447489962800676112166893475342566324961280"
def inputClause8406 : CNF.NClause := [(190,true),(193,true),(196,true),(204,true),(207,true),(214,false)]
theorem inputList8406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) inputClause8406 (by decide) v hb
mask_input "8406|26328072917139296674479506920917608079723773850137277813577744384|231513635479965406601982544454100954675291099091583636913258496"
def inputClause8423 : CNF.NClause := [(189,false),(195,true),(196,true),(202,true),(208,true),(212,true)]
theorem inputList8423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 13) (closed_mem 2 13) inputClause8423 (by decide) v hb
mask_input "8423|784637716923335095479473677900958302012794430558004314112|6999972771233810920599118933184261280580702697448512727401103360"
def inputClause8424 : CNF.NClause := [(187,true),(194,true),(196,true),(203,true),(210,true),(213,false)]
theorem inputList8424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) inputClause8424 (by decide) v hb
mask_input "8424|13164036458569648337239753460458804039861886925068638906788872192|1658485799869414928808355464952963434370811039891339126222356480"
def inputClause8435 : CNF.NClause := [(201,false),(202,true),(203,true),(204,true),(205,true),(216,true)]
theorem inputList8435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 15) (closed_mem 2 15) inputClause8435 (by decide) v hb
mask_input "8435|3213876088517980551083924184682325205044405987565585670602752|105408707951212726114450545409210902075046427580176078824429060096"
def inputClause8438 : CNF.NClause := [(190,true),(192,true),(199,true),(201,false),(208,true),(213,true)]
theorem inputList8438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 16) (closed_mem 2 16) inputClause8438 (by decide) v hb
mask_input "8438|3213876088517980551083924184682325205044405987565585670602752|13576223913299248576267221531881091256991852120918230849086816256"
def inputClause8447 : CNF.NClause := [(188,false),(194,true),(200,true),(201,true),(207,true),(212,true)]
theorem inputList8447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 17) (closed_mem 2 17) inputClause8447 (by decide) v hb
mask_input "8447|392318858461667547739736838950479151006397215279002157056|6792552221489693441438929107483787151527016464141643170956967936"
def inputClause8453 : CNF.NClause := [(189,false),(193,true),(197,true),(201,true),(210,true),(215,true)]
theorem inputList8453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 18) (closed_mem 2 18) inputClause8453 (by decide) v hb
mask_input "8453|784637716923335095479473677900958302012794430558004314112|54305077689147320518811037365417638050293475451980812853348139008"
def inputClause8461 : CNF.NClause := [(191,true),(192,true),(193,true),(194,true),(195,false),(216,true)]
theorem inputList8461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) inputClause8461 (by decide) v hb
mask_input "8461|50216813883093446110686315385661331328818843555712276103168|105312338746820202098023756452091106376393216168214944734569824256"
def inputClause8462 : CNF.NClause := [(191,true),(192,true),(193,true),(194,false),(195,true),(216,true)]
theorem inputList8462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) inputClause8462 (by decide) v hb
mask_input "8462|25108406941546723055343157692830665664409421777856138051584|105312363855227143644746811795248799207058880577636722590707875840"
def inputClause8465 : CNF.NClause := [(191,false),(192,true),(193,true),(194,true),(195,true),(216,true)]
theorem inputList8465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) inputClause8465 (by decide) v hb
mask_input "8465|3138550867693340381917894711603833208051177722232017256448|105312385825083217498129485220511780433891336935880778214828670976"
def inputClause8477 : CNF.NClause := [(188,false),(191,true),(199,true),(202,true),(210,true),(214,true)]
theorem inputList8477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 22) (closed_mem 2 22) inputClause8477 (by decide) v hb
mask_input "8477|392318858461667547739736838950479151006397215279002157056|27980811834210535866214796850785205420251067680420602476702466048"
def inputClause8483 : CNF.NClause := [(189,false),(191,true),(198,true),(205,true),(207,true),(213,true)]
theorem inputList8483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 23) (closed_mem 2 23) inputClause8483 (by decide) v hb
mask_input "8483|784637716923335095479473677900958302012794430558004314112|13421551418713019222235734803651186950749278006000053690663174144"
def inputClause8485 : CNF.NClause := [(187,true),(191,true),(200,true),(204,true),(208,false),(215,true)]
theorem inputList8485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 24) (closed_mem 2 24) inputClause8485 (by decide) v hb
mask_input "8485|411376139330301510538742295639337626245683966408394965837152256|52683467115741293107817382985168147002763208705545192976873947136"
def inputClause8493 : CNF.NClause := [(186,true),(187,true),(188,false),(189,true),(190,true),(216,true)]
theorem inputList8493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 25) (closed_mem 2 25) inputClause8493 (by decide) v hb
mask_input "8493|392318858461667547739736838950479151006397215279002157056|105312294316709481314173974926894095234629364693730314387575537664"
def inputClause8498 : CNF.NClause := [(186,true),(195,true),(199,true),(203,false),(207,true),(215,true)]
theorem inputList8498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) inputClause8498 (by decide) v hb
mask_input "8498|12855504354071922204335696738729300820177623950262342682411008|52862687687859471308229153591950650952822767355418504038518358016"
def inputClause8503 : CNF.NClause := [(186,true),(193,true),(200,true),(202,true),(209,false),(213,true)]
theorem inputList8503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) inputClause8503 (by decide) v hb
mask_input "8503|822752278660603021077484591278675252491367932816789931674304512|13172083801074128677395877877433566005827117896347745618784944128"
def inputClause8508 : CNF.NClause := [(186,true),(194,true),(197,true),(205,true),(208,true),(214,false)]
theorem inputList8508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) inputClause8508 (by decide) v hb
mask_input "8508|26328072917139296674479506920917608079723773850137277813577744384|463024230488777735280470105947700043137161898604748861559799808"
def inputClause8511 : CNF.NClause := [(186,true),(194,true),(197,false),(205,true),(208,true),(214,true)]
theorem inputList8511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) inputClause8511 (by decide) v hb
mask_input "8511|200867255532373784442745261542645325315275374222849104412672|26790896280372542035975534281603765477535620473367803826033131520"
def inputClause8516 : CNF.NClause := [(186,true),(192,true),(198,true),(204,false),(210,true),(212,true)]
theorem inputList8516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) inputClause8516 (by decide) v hb
mask_input "8516|25711008708143844408671393477458601640355247900524685364822016|8227930896298544960441382174033470760850513732871093298736922624"
def inputClause8518 : CNF.NClause := [(186,true),(192,false),(198,true),(204,true),(210,true),(212,true)]
theorem inputList8518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) inputClause8518 (by decide) v hb
mask_input "8518|6277101735386680763835789423207666416102355444464034512896|8253635627904953418169289731721506154824452878416173520067231744"
def inputClause8533 : CNF.NClause := [(221,true),(226,true),(231,true),(236,true),(241,false),(242,true)]
theorem inputList8533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) inputClause8533 (by decide) v hb
mask_input "8533|3533694129556768659166595001485837031654967793751237916243212402585239552|7181378283615583617215016476136478939251907638764030190508091007255445504"
def inputClause8563 : CNF.NClause := [(221,true),(225,true),(229,true),(233,true),(237,false),(246,true)]
theorem inputList8563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) inputClause8563 (by decide) v hb
mask_input "8563|220855883097298041197912187592864814478435487109452369765200775161577472|113092935646690194736488902571161183608760609485537373289929039591875018752"
def inputClause8590 : CNF.NClause := [(227,true),(228,false),(229,true),(230,true),(231,true),(247,true)]
theorem inputList8590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) inputClause8590 (by decide) v hb
mask_input "8590|431359146674410236714672241392314090778194310760649159697657763987456|226162678999259973135094442842593758580234222617585256052381209803033149440"
def inputClause8591 : CNF.NClause := [(227,false),(228,true),(229,true),(230,true),(231,true),(247,true)]
theorem inputList8591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) inputClause8591 (by decide) v hb
mask_input "8591|215679573337205118357336120696157045389097155380324579848828881993728|226162894678833310340212800178714454737279611714740636376961058631915143168"
def inputClause8617 : CNF.NClause := [(232,true),(233,true),(234,true),(235,true),(236,false),(247,true)]
theorem inputList8617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) inputClause8617 (by decide) v hb
mask_input "8617|110427941548649020598956093796432407239217743554726184882600387580788736|226259950486835052643473601433027725407704705434661782437893031628812320768"
def inputClause8618 : CNF.NClause := [(232,true),(233,true),(234,true),(235,false),(236,true),(247,true)]
theorem inputList8618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) inputClause8618 (by decide) v hb
mask_input "8618|55213970774324510299478046898216203619608871777363092441300193790394368|226315164457609377153773079479925941611324314306439145530334331822602715136"
def inputClause8622 : CNF.NClause := [(221,true),(223,true),(230,true),(232,true),(239,true),(244,false)]
theorem inputList8622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) inputClause8622 (by decide) v hb
mask_input "8622|28269553036454149273332760011886696253239742350009903329945699220681916416|892067565289347338675813862083734926998476857868286550112556945682464768"
def inputClause8623 : CNF.NClause := [(221,true),(223,true),(230,true),(232,true),(239,false),(244,true)]
theorem inputList8623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) inputClause8623 (by decide) v hb
mask_input "8623|883423532389192164791648750371459257913741948437809479060803100646309888|28278197069354304447216925123598971922324477259440380400997453065718071296"
def inputClause8625 : CNF.NClause := [(221,true),(223,true),(230,false),(232,true),(239,true),(244,true)]
theorem inputList8625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) inputClause8625 (by decide) v hb
mask_input "8625|1725436586697640946858688965569256363112777243042596638790631055949824|29159895165156798971061715185004861923875106430635147283419465535308431360"
def inputClause8626 : CNF.NClause := [(221,true),(223,false),(230,true),(232,true),(239,true),(244,true)]
theorem inputList8626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) inputClause8626 (by decide) v hb
mask_input "8626|13479973333575319897333507543509815336818572211270286240551805124608|29161607121770163036688676540462887670422882389305978609772015614559256576"
def inputClause8650 : CNF.NClause := [(222,true),(223,false),(224,true),(225,true),(226,true),(247,true)]
theorem inputList8650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) inputClause8650 (by decide) v hb
mask_input "8650|13479973333575319897333507543509815336818572211270286240551805124608|226156619751246531028800591430952950918240322669376290058716081766629638144"
def inputClause8656 : CNF.NClause := [(221,true),(222,false),(228,true),(234,true),(240,true),(243,true)]
theorem inputList8656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) inputClause8656 (by decide) v hb
mask_input "8656|6739986666787659948666753771754907668409286105635143120275902562304|15929665297532629025466105535753652935801771906723065636046363704244043776"
def inputClause8688 : CNF.NClause := [(217,true),(224,true),(231,true),(233,true),(240,true),(244,false)]
theorem inputList8688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) inputClause8688 (by decide) v hb
mask_input "8688|28269553036454149273332760011886696253239742350009903329945699220681916416|1784128601216611226806052453249753466430149944240658266180216124084322304"
def inputClause8698 : CNF.NClause := [(217,true),(225,false),(228,true),(236,true),(239,true),(245,true)]
theorem inputList8698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) inputClause8698 (by decide) v hb
mask_input "8698|53919893334301279589334030174039261347274288845081144962207220498432|57533389116617397479407212936018731853064087224113293774092722095976873984"
def inputClause8702 : CNF.NClause := [(217,true),(223,true),(229,true),(235,false),(241,true),(243,true)]
theorem inputList8702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) inputClause8702 (by decide) v hb
mask_input "8702|55213970774324510299478046898216203619608871777363092441300193790394368|17669347056675109028740675081255568663612596813740112950919920388881252352"
def inputClause8901 : CNF.NClause := [(304,true),(305,true),(306,false),(307,true),(308,true),(309,true)]
theorem inputList8901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 0) (closed_mem 5 0) inputClause8901 (by decide) v hb
mask_input "8901|130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064|1922961961659754865437412729858452984032586163620643820600516584190535946976589850637127122944"
def inputClause8909 : CNF.NClause := [(283,false),(288,true),(293,true),(298,true),(303,true),(304,true)]
theorem inputList8909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) inputClause8909 (by decide) v hb
mask_input "8909|15541351137805832567355695254588151253139254712417116170014499277911234281641667985408|49414534092912810551200935558116265493221423599375266552601941208081220782662328726339977216"
end Percolation.MaskChain
