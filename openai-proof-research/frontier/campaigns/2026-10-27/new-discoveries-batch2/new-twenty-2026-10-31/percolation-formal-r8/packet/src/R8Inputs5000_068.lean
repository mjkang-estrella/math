import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8560 : CNF.NClause := [(237,true),(238,false),(239,true),(240,true),(241,true),(247,true)]
theorem inputList8560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) inputClause8560 (by decide) v hb
mask_input "8560|441711766194596082395824375185729628956870974218904739530401550323154944|232561244901454837381401533535286649645792567926253345362756416245141078016"
def inputClause8561 : CNF.NClause := [(237,false),(238,true),(239,true),(240,true),(241,true),(247,true)]
theorem inputList8561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) inputClause8561 (by decide) v hb
mask_input "8561|220855883097298041197912187592864814478435487109452369765200775161577472|232782100784552135422599445722879514460271003413362797732521617020302655488"
def inputClause8566 : CNF.NClause := [(221,true),(225,false),(229,true),(233,true),(237,true),(246,true)]
theorem inputList8566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) inputClause8566 (by decide) v hb
mask_input "8566|53919893334301279589334030174039261347274288845081144962207220498432|113313737609894158476407225424723874383977697698357980578549278159816097792"
def inputClause8571 : CNF.NClause := [(219,true),(226,true),(228,false),(235,true),(237,true),(244,true)]
theorem inputList8571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) inputClause8571 (by decide) v hb
mask_input "8571|431359146674410236714672241392314090778194310760649159697657763987456|28545731572610773775846822497782346819223939808635172158835014638562705408"
def inputClause8579 : CNF.NClause := [(220,false),(223,true),(231,true),(234,true),(237,true),(245,true)]
theorem inputList8579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 8) (closed_mem 3 8) inputClause8579 (by decide) v hb
mask_input "8579|1684996666696914987166688442938726917102321526408785780068975640576|56791033294539487700226785946254047445309286996076237039441071127337631744"
def inputClause8581 : CNF.NClause := [(218,true),(224,true),(230,true),(236,true),(237,false),(243,true)]
theorem inputList8581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) inputClause8581 (by decide) v hb
mask_input "8581|220855883097298041197912187592864814478435487109452369765200775161577472|14246957277558255123080736247392547544534604608527524589263166749831856128"
def inputClause8584 : CNF.NClause := [(218,true),(224,false),(230,true),(236,true),(237,true),(243,true)]
theorem inputList8584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) inputClause8584 (by decide) v hb
mask_input "8584|26959946667150639794667015087019630673637144422540572481103610249216|14467786200708886013638853767970325339382366458492554418455886421383184384"
def inputClause8585 : CNF.NClause := [(218,false),(224,true),(230,true),(236,true),(237,true),(243,true)]
theorem inputList8585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) inputClause8585 (by decide) v hb
mask_input "8585|421249166674228746791672110734681729275580381602196445017243910144|14467812739406386490049901643313301624331310820056595356831922507749523456"
def inputClause8595 : CNF.NClause := [(221,true),(224,true),(227,false),(235,true),(238,true),(245,true)]
theorem inputList8595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) inputClause8595 (by decide) v hb
mask_input "8595|215679573337205118357336120696157045389097155380324579848828881993728|57036062139817219683830591446249311236140472387803549850007141427038912512"
def inputClause8597 : CNF.NClause := [(221,false),(224,true),(227,true),(235,true),(238,true),(245,true)]
theorem inputList8597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) inputClause8597 (by decide) v hb
mask_input "8597|3369993333393829974333376885877453834204643052817571560137951281152|57036274449397223495118974448993121515732027280315877357015430117969625088"
def inputClause8601 : CNF.NClause := [(219,true),(223,true),(227,false),(236,true),(240,true),(246,true)]
theorem inputList8601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) inputClause8601 (by decide) v hb
mask_input "8601|215679573337205118357336120696157045389097155380324579848828881993728|114955501474615297367290684558937900915204466410202932937466134057894019072"
def inputClause8609 : CNF.NClause := [(220,false),(226,true),(227,true),(233,true),(239,true),(243,true)]
theorem inputList8609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 13) (closed_mem 3 13) inputClause8609 (by decide) v hb
mask_input "8609|1684996666696914987166688442938726917102321526408785780068975640576|15032327062669853736710434272220405671006598987120172404013751002757857280"
def inputClause8613 : CNF.NClause := [(218,true),(225,true),(227,false),(234,true),(241,true),(244,true)]
theorem inputList8613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) inputClause8613 (by decide) v hb
mask_input "8613|215679573337205118357336120696157045389097155380324579848828881993728|31830908492540581163157430162523926160647591129519049475750968944626761728"
def inputClause8614 : CNF.NClause := [(218,true),(225,false),(227,true),(234,true),(241,true),(244,true)]
theorem inputList8614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) inputClause8614 (by decide) v hb
mask_input "8614|53919893334301279589334030174039261347274288845081144962207220498432|31831070252220584066996198164614448278431632952385584719185855566288257024"
def inputClause8619 : CNF.NClause := [(232,true),(233,true),(234,false),(235,true),(236,true),(247,true)]
theorem inputList8619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) inputClause8619 (by decide) v hb
mask_input "8619|27606985387162255149739023449108101809804435888681546220650096895197184|226342771442996539408922818503375049713134118742327827076554981919497912320"
def inputClause8620 : CNF.NClause := [(232,true),(233,false),(234,true),(235,true),(236,true),(247,true)]
theorem inputList8620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) inputClause8620 (by decide) v hb
mask_input "8620|13803492693581127574869511724554050904902217944340773110325048447598592|226356574935690120536497688015099603764039020960272167849665306967945510912"
def inputClause8621 : CNF.NClause := [(232,false),(233,true),(234,true),(235,true),(236,true),(247,true)]
theorem inputList8621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) inputClause8621 (by decide) v hb
mask_input "8621|6901746346790563787434755862277025452451108972170386555162524223799296|226363476682036911100285122770961880789491472069244338236220469492169310208"
def inputClause8627 : CNF.NClause := [(221,false),(223,true),(230,true),(232,true),(239,true),(244,true)]
theorem inputList8627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) inputClause8627 (by decide) v hb
mask_input "8627|3369993333393829974333376885877453834204643052817571560137951281152|29161617231750163218178599540593545302784385003235137062486696028413100032"
def inputClause8632 : CNF.NClause := [(219,true),(225,false),(231,true),(232,true),(238,true),(243,true)]
theorem inputList8632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) inputClause8632 (by decide) v hb
mask_input "8632|53919893334301279589334030174039261347274288845081144962207220498432|14586841746440189913200850098266714763118877363842875188728884981487632384"
def inputClause8639 : CNF.NClause := [(220,false),(224,true),(228,true),(232,true),(241,true),(246,true)]
theorem inputList8639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 18) (closed_mem 3 18) inputClause8639 (by decide) v hb
mask_input "8639|1684996666696914987166688442938726917102321526408785780068975640576|116619266340813497877161579144151378403787840134218204812313350570910941184"
def inputClause8645 : CNF.NClause := [(218,false),(226,true),(229,true),(232,true),(240,true),(245,true)]
theorem inputList8645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) inputClause8645 (by decide) v hb
mask_input "8645|421249166674228746791672110734681729275580381602196445017243910144|58313825442113490863068860292921720754463670643066807465177486896849223680"
def inputClause8648 : CNF.NClause := [(222,true),(223,true),(224,true),(225,false),(226,true),(247,true)]
theorem inputList8648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) inputClause8648 (by decide) v hb
mask_input "8648|53919893334301279589334030174039261347274288845081144962207220498432|226156579311326530302840899430430320388794312213659656247857360111214264320"
def inputClause8651 : CNF.NClause := [(222,false),(223,true),(224,true),(225,true),(226,true),(247,true)]
theorem inputList8651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) inputClause8651 (by decide) v hb
mask_input "8651|6739986666787659948666753771754907668409286105635143120275902562304|226156626491233197816460540097706722673147991078662395693859202042532200448"
def inputClause8657 : CNF.NClause := [(221,false),(222,true),(228,true),(234,true),(240,true),(243,true)]
theorem inputList8657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) inputClause8657 (by decide) v hb
mask_input "8657|3369993333393829974333376885877453834204643052817571560137951281152|15929668667525962419296079869130538813255606111366118453617923842195324928"
def inputClause8662 : CNF.NClause := [(219,true),(222,false),(230,true),(233,true),(241,true),(245,true)]
theorem inputList8662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) inputClause8662 (by decide) v hb
mask_input "8662|6739986666787659948666753771754907668409286105635143120275902562304|60088329974243679322811336809293574314765926040119191150276616557940441088"
def inputClause8669 : CNF.NClause := [(220,false),(222,true),(229,true),(236,true),(238,true),(244,true)]
theorem inputList8669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 23) (closed_mem 3 23) inputClause8669 (by decide) v hb
mask_input "8669|1684996666696914987166688442938726917102321526408785780068975640576|28822562202477409984460918492105414672525055865691161187821216750016397312"
def inputClause8675 : CNF.NClause := [(218,false),(222,true),(231,true),(235,true),(239,true),(246,true)]
theorem inputList8675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) inputClause8675 (by decide) v hb
mask_input "8675|421249166674228746791672110734681729275580381602196445017243910144|114020307262140175837975832889501370742126214184026976719705601715178831872"
def inputClause8678 : CNF.NClause := [(217,true),(218,true),(219,true),(220,false),(221,true),(247,true)]
theorem inputList8678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 25) (closed_mem 3 25) inputClause8678 (by decide) v hb
mask_input "8678|1684996666696914987166688442938726917102321526408785780068975640576|226156429135998610940292668199322843474757825469253615064824711463760297984"
def inputClause8683 : CNF.NClause := [(217,true),(226,true),(230,true),(234,true),(238,false),(246,true)]
theorem inputList8683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) inputClause8683 (by decide) v hb
mask_input "8683|441711766194596082395824375185729628956870974218904739530401550323154944|113107652618201708929101189823857865816995445799539218426030384533741764608"
def inputClause8684 : CNF.NClause := [(217,true),(226,true),(230,true),(234,false),(238,true),(246,true)]
theorem inputList8684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) inputClause8684 (by decide) v hb
mask_input "8684|27606985387162255149739023449108101809804435888681546220650096895197184|113521757399009142756347275175594487344142512337869441619340135987169722368"
def inputClause8686 : CNF.NClause := [(217,true),(226,false),(230,true),(234,true),(238,true),(246,true)]
theorem inputList8686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) inputClause8686 (by decide) v hb
mask_input "8686|107839786668602559178668060348078522694548577690162289924414440996864|113549256544609636408937835530983247367429622225180433003270861669623922688"
def inputClause8689 : CNF.NClause := [(217,true),(224,true),(231,true),(233,true),(240,false),(244,true)]
theorem inputList8689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) inputClause8689 (by decide) v hb
mask_input "8689|1766847064778384329583297500742918515827483896875618958121606201292619776|28286834572892376170555514964393531203842408397374942638004309143473618944"
def inputClause8691 : CNF.NClause := [(217,true),(224,true),(231,false),(233,true),(240,true),(244,true)]
theorem inputList8691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) inputClause8691 (by decide) v hb
mask_input "8691|3450873173395281893717377931138512726225554486085193277581262111899648|30050230764497365218245095087205311206943666739764476402848334082654339072"
def inputClause8692 : CNF.NClause := [(217,true),(224,false),(231,true),(233,true),(240,true),(244,true)]
theorem inputList8692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) inputClause8692 (by decide) v hb
mask_input "8692|26959946667150639794667015087019630673637144422540572481103610249216|30053654677724093349499017798121362700039218657106139055553434241155989504"
def inputClause8700 : CNF.NClause := [(217,true),(223,true),(229,true),(235,true),(241,true),(243,false)]
theorem inputList8700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) inputClause8700 (by decide) v hb
mask_input "8700|14134776518227074636666380005943348126619871175004951664972849610340958208|3589784509222358902373773122210436740612334510512524378388370972330688512"
def inputClause8701 : CNF.NClause := [(217,true),(223,true),(229,true),(235,true),(241,false),(243,true)]
theorem inputList8701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) inputClause8701 (by decide) v hb
mask_input "8701|3533694129556768659166595001485837031654967793751237916243212402585239552|14190866897892664879873558126667947835577237891766238127118008180086407168"
def inputClause8703 : CNF.NClause := [(217,true),(223,true),(229,false),(235,true),(241,true),(243,true)]
theorem inputList8703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) inputClause8703 (by decide) v hb
mask_input "8703|862718293348820473429344482784628181556388621521298319395315527974912|17723698309156084718566723783671000239050649296895954745041825267143671808"
def inputClause8704 : CNF.NClause := [(217,true),(223,false),(229,true),(235,true),(241,true),(243,true)]
theorem inputList8704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) inputClause8704 (by decide) v hb
mask_input "8704|13479973333575319897333507543509815336818572211270286240551805124608|17724547547476099963720255794646241357416868866945264773074980030866522112"
def inputClause8709 : CNF.NClause := [(217,true),(222,true),(227,false),(232,true),(237,true),(242,true)]
theorem inputList8709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) inputClause8709 (by decide) v hb
mask_input "8709|215679573337205118357336120696157045389097155380324579848828881993728|7295152839168876048092859009016643025489355230660395025048130889080373248"
def inputClause8710 : CNF.NClause := [(217,true),(222,false),(227,true),(232,true),(237,true),(242,true)]
theorem inputList8710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) inputClause8710 (by decide) v hb
mask_input "8710|6739986666787659948666753771754907668409286105635143120275902562304|7295361778755546465551267678383567427627075918529669714484859442059804672"
end Percolation.MaskChain
