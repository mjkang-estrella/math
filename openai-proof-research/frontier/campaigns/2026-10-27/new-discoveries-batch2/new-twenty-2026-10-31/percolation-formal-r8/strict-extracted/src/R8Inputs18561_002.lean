import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8397 : CNF.NClause := [(187,true),(193,true),(199,false),(205,true),(206,true),(212,true)]
theorem inputList8397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 9) (closed_mem 2 9) inputClause8397 (by decide) v hb
mask_input "8397|803469022129495137770981046170581301261101496891396417650688|6736297031896587239267206632541419520345482657846964133153472512"
def inputClause8398 : CNF.NClause := [(187,true),(193,false),(199,true),(205,true),(206,true),(212,true)]
theorem inputList8398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 9) (closed_mem 2 9) inputClause8398 (by decide) v hb
mask_input "8398|12554203470773361527671578846415332832204710888928069025792|6737087946715245961043449942008743686313911554632966601502097408"
def inputClause8402 : CNF.NClause := [(196,true),(197,true),(198,true),(199,false),(200,true),(216,true)]
theorem inputList8402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) inputClause8402 (by decide) v hb
mask_input "8402|803469022129495137770981046170581301261101496891396417650688|105314601641995808996439119254178172740136221067352674019011723264"
def inputClause8405 : CNF.NClause := [(196,false),(197,true),(198,true),(199,true),(200,true),(216,true)]
theorem inputList8405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) inputClause8405 (by decide) v hb
mask_input "8405|100433627766186892221372630771322662657637687111424552206336|105315304677390172304684668862593571998774824531162453990877167616"
def inputClause8407 : CNF.NClause := [(190,true),(193,true),(196,true),(204,true),(207,false),(214,true)]
theorem inputList8407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) inputClause8407 (by decide) v hb
mask_input "8407|205688069665150755269371147819668813122841983204197482918576128|26353898482954111325812118317552040221276222966024663967572426752"
def inputClause8408 : CNF.NClause := [(190,true),(193,true),(196,true),(204,false),(207,true),(214,true)]
theorem inputList8408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) inputClause8408 (by decide) v hb
mask_input "8408|25711008708143844408671393477458601640355247900524685364822016|26533875543911118236672818071894250432758709701328336765126180864"
def inputClause8411 : CNF.NClause := [(190,false),(193,true),(196,true),(204,true),(207,true),(214,true)]
theorem inputList8411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) inputClause8411 (by decide) v hb
mask_input "8411|1569275433846670190958947355801916604025588861116008628224|26559584983343828234411298506424353232482460923640000334482374656"
def inputClause8417 : CNF.NClause := [(188,false),(192,true),(196,true),(205,true),(209,true),(215,true)]
theorem inputList8417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 12) (closed_mem 2 12) inputClause8417 (by decide) v hb
mask_input "8417|392318858461667547739736838950479151006397215279002157056|53530426841084985632426826428489003145548699868934950818146156544"
def inputClause8420 : CNF.NClause := [(189,true),(195,true),(196,true),(202,false),(208,true),(212,true)]
theorem inputList8420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 13) (closed_mem 2 13) inputClause8420 (by decide) v hb
mask_input "8420|6427752177035961102167848369364650410088811975131171341205504|6993545803694491882832046564288574531128915898267812114064211968"
def inputClause8426 : CNF.NClause := [(187,true),(194,true),(196,true),(203,false),(210,true),(213,true)]
theorem inputList8426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) inputClause8426 (by decide) v hb
mask_input "8426|12855504354071922204335696738729300820177623950262342682411008|14809666754084991343843773228673038173412520341009715690328817664"
def inputClause8427 : CNF.NClause := [(187,true),(194,true),(196,false),(203,true),(210,true),(213,true)]
theorem inputList8427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) inputClause8427 (by decide) v hb
mask_input "8427|100433627766186892221372630771322662657637687111424552206336|14822421824811297079155887552780996151570040327272866608459022336"
def inputClause8428 : CNF.NClause := [(187,true),(194,false),(196,true),(203,true),(210,true),(213,true)]
theorem inputList8428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) inputClause8428 (by decide) v hb
mask_input "8428|25108406941546723055343157692830665664409421777856138051584|14822497150032121719325053582254074643567033555538200176873177088"
def inputClause8431 : CNF.NClause := [(201,true),(202,true),(203,true),(204,true),(205,false),(216,true)]
theorem inputList8431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 15) (closed_mem 2 15) inputClause8431 (by decide) v hb
mask_input "8431|51422017416287688817342786954917203280710495801049370729644032|105360499809884956406184286546440667196970761490362595039370018816"
def inputClause8433 : CNF.NClause := [(201,true),(202,true),(203,false),(204,true),(205,true),(216,true)]
theorem inputList8433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 15) (closed_mem 2 15) inputClause8433 (by decide) v hb
mask_input "8433|12855504354071922204335696738729300820177623950262342682411008|105399066322947172172797293636656855099431294362213382067417251840"
def inputClause8439 : CNF.NClause := [(190,true),(192,true),(199,false),(201,true),(208,true),(213,true)]
theorem inputList8439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 16) (closed_mem 2 16) inputClause8439 (by decide) v hb
mask_input "8439|803469022129495137770981046170581301261101496891396417650688|13578634320365637061680534475019603000895635425408905038339768320"
def inputClause8448 : CNF.NClause := [(189,true),(193,true),(197,true),(201,true),(210,true),(215,false)]
theorem inputList8448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 18) (closed_mem 2 18) inputClause8448 (by decide) v hb
mask_input "8448|52656145834278593348959013841835216159447547700274555627155488768|1648932639506444093187119003056099791804229764500687784196964352"
def inputClause8454 : CNF.NClause := [(187,true),(195,true),(198,true),(201,true),(209,true),(214,false)]
theorem inputList8454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 19) (closed_mem 2 19) inputClause8454 (by decide) v hb
mask_input "8454|26328072917139296674479506920917608079723773850137277813577744384|826418302233498073477338562170248004917947211594964567330914304"
def inputClause8455 : CNF.NClause := [(187,true),(195,true),(198,true),(201,true),(209,false),(214,true)]
theorem inputList8455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 19) (closed_mem 2 19) inputClause8455 (by decide) v hb
mask_input "8455|822752278660603021077484591278675252491367932816789931674304512|26331738940712191726879360891809180832150353128915452449234354176"
def inputClause8459 : CNF.NClause := [(187,false),(195,true),(198,true),(201,true),(209,true),(214,true)]
theorem inputList8459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 19) (closed_mem 2 19) inputClause8459 (by decide) v hb
mask_input "8459|196159429230833773869868419475239575503198607639501078528|27154491023213365517123071613219436609402145558533634741407580160"
def inputClause8463 : CNF.NClause := [(191,true),(192,true),(193,false),(194,true),(195,true),(216,true)]
theorem inputList8463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) inputClause8463 (by decide) v hb
mask_input "8463|12554203470773361527671578846415332832204710888928069025792|105312376409430614418108339466827645622391712782347611518776901632"
def inputClause8467 : CNF.NClause := [(190,true),(191,true),(197,true),(203,true),(209,false),(212,true)]
theorem inputList8467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 21) (closed_mem 2 21) inputClause8467 (by decide) v hb
mask_input "8467|822752278660603021077484591278675252491367932816789931674304512|6595079308720730004619228049071741371826248438625387993207144448"
def inputClause8479 : CNF.NClause := [(189,true),(191,true),(198,true),(205,true),(207,false),(213,true)]
theorem inputList8479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 23) (closed_mem 2 23) inputClause8479 (by decide) v hb
mask_input "8479|205688069665150755269371147819668813122841983204197482918576128|13215864133685585390301459135305196038584738035590286765748912128"
def inputClause8480 : CNF.NClause := [(189,true),(191,true),(198,true),(205,false),(207,true),(213,true)]
theorem inputList8480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 23) (closed_mem 2 23) inputClause8480 (by decide) v hb
mask_input "8480|51422017416287688817342786954917203280710495801049370729644032|13370130185934448456753487496169947648426869522993434877937844224"
def inputClause8484 : CNF.NClause := [(187,true),(191,true),(200,true),(204,true),(208,true),(215,false)]
theorem inputList8484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 24) (closed_mem 2 24) inputClause8484 (by decide) v hb
mask_input "8484|52656145834278593348959013841835216159447547700274555627155488768|438697420793001269397111438972268469561344971679032315555610624"
def inputClause8496 : CNF.NClause := [(186,true),(195,true),(199,true),(203,true),(207,true),(215,false)]
theorem inputList8496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) inputClause8496 (by decide) v hb
mask_input "8496|52656145834278593348959013841835216159447547700274555627155488768|219397357934949881474475446854164094195397279094210754045280256"
def inputClause8497 : CNF.NClause := [(186,true),(195,true),(199,true),(203,true),(207,false),(215,true)]
theorem inputList8497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) inputClause8497 (by decide) v hb
mask_input "8497|205688069665150755269371147819668813122841983204197482918576128|52669855122548392475164118140869711440520102996164568898282192896"
def inputClause8499 : CNF.NClause := [(186,true),(195,true),(199,false),(203,true),(207,true),(215,true)]
theorem inputList8499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) inputClause8499 (by decide) v hb
mask_input "8499|803469022129495137770981046170581301261101496891396417650688|52874739723191413735295718307643209672341683877871874984783118336"
def inputClause8502 : CNF.NClause := [(186,true),(193,true),(200,true),(202,true),(209,true),(213,false)]
theorem inputList8502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) inputClause8502 (by decide) v hb
mask_input "8502|13164036458569648337239753460458804039861886925068638906788872192|830799621165083361233609008253437218456598904095896643670376448"
def inputClause8504 : CNF.NClause := [(186,true),(193,true),(200,true),(202,false),(209,true),(213,true)]
theorem inputList8504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) inputClause8504 (by decide) v hb
mask_input "8504|6427752177035961102167848369364650410088811975131171341205504|13988408327557695737371194620342876607908397017189404379118043136"
def inputClause8506 : CNF.NClause := [(186,true),(193,false),(200,true),(202,true),(209,true),(213,true)]
theorem inputList8506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) inputClause8506 (by decide) v hb
mask_input "8506|12554203470773361527671578846415332832204710888928069025792|13994823525531260925111834797133394842985653624453646622390222848"
def inputClause8509 : CNF.NClause := [(186,true),(194,true),(197,true),(205,true),(208,false),(214,true)]
theorem inputList8509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) inputClause8509 (by decide) v hb
mask_input "8509|411376139330301510538742295639337626245683966408394965837152256|26379721008297772899221234731225970496615251782333631709300391936"
def inputClause8510 : CNF.NClause := [(186,true),(194,true),(197,true),(205,false),(208,true),(214,true)]
theorem inputList8510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) inputClause8510 (by decide) v hb
mask_input "8510|51422017416287688817342786954917203280710495801049370729644032|26739675130211786720942634239910390919580225252940977304407900160"
def inputClause8512 : CNF.NClause := [(186,true),(194,false),(197,true),(205,true),(208,true),(214,true)]
theorem inputList8512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) inputClause8512 (by decide) v hb
mask_input "8512|25108406941546723055343157692830665664409421777856138051584|26791072039221132863036921683707615292195271339320248818999492608"
def inputClause8515 : CNF.NClause := [(186,true),(192,true),(198,true),(204,true),(210,false),(212,true)]
theorem inputList8515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) inputClause8515 (by decide) v hb
mask_input "8515|1645504557321206042154969182557350504982735865633579863348609024|6608137347685482762695084384953578857508133115138038120753135616"
def inputClause8517 : CNF.NClause := [(186,true),(192,true),(198,false),(204,true),(210,true),(212,true)]
theorem inputList8517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) inputClause8517 (by decide) v hb
mask_input "8517|401734511064747568885490523085290650630550748445698208825344|8253240170495624057281168076987844071840238430023172285892919296"
def inputClause8521 : CNF.NClause := [(186,true),(191,true),(196,true),(201,true),(206,false),(211,true)]
theorem inputList8521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) inputClause8521 (by decide) v hb
mask_input "8521|102844034832575377634685573909834406561420991602098741459288064|3294326660989278560510512514759075999286169577718862788687822848"
def inputClause8522 : CNF.NClause := [(186,true),(191,true),(196,true),(201,false),(206,true),(211,true)]
theorem inputList8522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) inputClause8522 (by decide) v hb
mask_input "8522|3213876088517980551083924184682325205044405987565585670602752|3393956819733335957594114164484228080642546163333395944476508160"
def inputClause8523 : CNF.NClause := [(186,true),(191,true),(196,false),(201,true),(206,true),(211,true)]
theorem inputList8523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) inputClause8523 (by decide) v hb
mask_input "8523|100433627766186892221372630771322662657637687111424552206336|3397070262194087751252976716038139083184932931633850105594904576"
def inputClause8524 : CNF.NClause := [(186,true),(191,false),(196,true),(201,true),(206,true),(211,true)]
theorem inputList8524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) inputClause8524 (by decide) v hb
mask_input "8524|3138550867693340381917894711603833208051177722232017256448|3397167557270986244804816170774198802014382518143239298129854464"
def inputClause8535 : CNF.NClause := [(221,true),(226,true),(231,false),(236,true),(241,true),(242,true)]
theorem inputList8535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) inputClause8535 (by decide) v hb
mask_input "8535|3450873173395281893717377931138512726225554486085193277581262111899648|10711621539998956994487894099691177458180649878029182913473722147728785408"
end Percolation.MaskChain
