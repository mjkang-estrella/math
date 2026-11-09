import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8260 : CNF.NClause := [(157,true),(163,false),(169,true),(170,true),(176,true),(181,true)]
theorem inputList8260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 17) (closed_mem 1 17) inputClause8260 (by decide) v hb
mask_input "8260|11692013098647223345629478661730264157247460343808|3163017102238540703609316378861168991467218408881258496"
def inputClause8264 : CNF.NClause := [(158,true),(162,true),(166,true),(170,false),(179,true),(184,true)]
theorem inputList8264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 18) (closed_mem 1 18) inputClause8264 (by decide) v hb
mask_input "8264|1496577676626844588240573268701473812127674924007424|25286276171773913997036893349469934416025287033425494016"
def inputClause8267 : CNF.NClause := [(158,false),(162,true),(166,true),(170,true),(179,true),(184,true)]
theorem inputList8267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 18) (closed_mem 1 18) inputClause8267 (by decide) v hb
mask_input "8267|365375409332725729550921208179070754913983135744|25287772384075131508899404371817427710766659794366365696"
def inputClause8273 : CNF.NClause := [(156,false),(164,true),(167,true),(170,true),(178,true),(183,true)]
theorem inputList8273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 19) (closed_mem 1 19) inputClause8273 (by decide) v hb
mask_input "8273|91343852333181432387730302044767688728495783936|12644795246055985576064824877874663383421555887224913920"
def inputClause8278 : CNF.NClause := [(160,true),(161,false),(162,true),(163,true),(164,true),(185,true)]
theorem inputList8278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 20) (closed_mem 1 20) inputClause8278 (by decide) v hb
mask_input "8278|2923003274661805836407369665432566039311865085952|49039899691255926063651732775670042648007221931919015936"
def inputClause8280 : CNF.NClause := [(159,true),(160,true),(166,true),(172,true),(178,true),(181,false)]
theorem inputList8280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) inputClause8280 (by decide) v hb
mask_input "8280|3064991081731777716716694054300618367237478244367204352|389205924280224767083691391218926107690982943823495168"
def inputClause8283 : CNF.NClause := [(159,true),(160,true),(166,false),(172,true),(178,true),(181,true)]
theorem inputList8283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) inputClause8283 (by decide) v hb
mask_input "8283|93536104789177786765035829293842113257979682750464|3454103469907213306013620409690250632815203208507949056"
def inputClause8291 : CNF.NClause := [(157,false),(160,true),(168,true),(171,true),(179,true),(183,true)]
theorem inputList8291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 22) (closed_mem 1 22) inputClause8291 (by decide) v hb
mask_input "8291|182687704666362864775460604089535377456991567872|13029580858634103027272409224317039093119589463072178176"
def inputClause8296 : CNF.NClause := [(158,true),(160,false),(167,true),(174,true),(176,true),(182,true)]
theorem inputList8296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 23) (closed_mem 1 23) inputClause8296 (by decide) v hb
mask_input "8296|1461501637330902918203684832716283019655932542976|6249895815178690688791893592677150502742441356003639296"
def inputClause8308 : CNF.NClause := [(155,true),(156,false),(157,true),(158,true),(159,true),(185,true)]
theorem inputList8308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 25) (closed_mem 1 25) inputClause8308 (by decide) v hb
mask_input "8308|91343852333181432387730302044767688728495783936|49039858632194302298597874490899273524931138473064136704"
def inputClause8313 : CNF.NClause := [(155,true),(164,true),(168,false),(172,true),(176,true),(184,true)]
theorem inputList8313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) inputClause8313 (by decide) v hb
mask_input "8313|374144419156711147060143317175368453031918731001856|24621719365562970626771318869499121640036666708938719232"
def inputClause8314 : CNF.NClause := [(155,true),(164,false),(168,true),(172,true),(176,true),(184,true)]
theorem inputList8314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) inputClause8314 (by decide) v hb
mask_input "8314|23384026197294446691258957323460528314494920687616|24622070125955930043471687753858973547961384132749033472"
def inputClause8316 : CNF.NClause := [(155,true),(162,true),(169,true),(171,true),(178,true),(182,false)]
theorem inputList8316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) inputClause8316 (by decide) v hb
mask_input "8316|6129982163463555433433388108601236734474956488734408704|386871221086514816262577198563812867950926955833982976"
def inputClause8319 : CNF.NClause := [(155,true),(162,true),(169,false),(171,true),(178,true),(182,true)]
theorem inputList8319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) inputClause8319 (by decide) v hb
mask_input "8319|748288838313422294120286634350736906063837462003712|6516105095711756827401845020530698865519819607106387968"
def inputClause8320 : CNF.NClause := [(155,true),(162,false),(169,true),(171,true),(178,true),(182,true)]
theorem inputList8320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) inputClause8320 (by decide) v hb
mask_input "8320|5846006549323611672814739330865132078623730171904|6516847538543520926084292492425718737293804820838219776"
def inputClause8323 : CNF.NClause := [(155,true),(163,true),(166,true),(174,true),(177,false),(183,true)]
theorem inputList8323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) inputClause8323 (by decide) v hb
mask_input "8323|191561942608236107294793378393788647952342390272950272|12284014843542954371879452248674803644705215367643922432"
def inputClause8326 : CNF.NClause := [(155,true),(163,false),(166,true),(174,true),(177,true),(183,true)]
theorem inputList8326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) inputClause8326 (by decide) v hb
mask_input "8326|11692013098647223345629478661730264157247460343808|12475565094138091831950899997589930562393400510456528896"
def inputClause8328 : CNF.NClause := [(155,true),(161,true),(167,true),(173,true),(179,true),(181,false)]
theorem inputList8328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) inputClause8328 (by decide) v hb
mask_input "8328|3064991081731777716716694054300618367237478244367204352|778410432730738369855180772618170521482790595962339328"
def inputClause8329 : CNF.NClause := [(155,true),(161,true),(167,true),(173,true),(179,false),(181,true)]
theorem inputList8329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) inputClause8329 (by decide) v hb
mask_input "8329|766247770432944429179173513575154591809369561091801088|3077153744029571657392701313343634296910899279237742592"
def inputClause8330 : CNF.NClause := [(155,true),(161,true),(167,true),(173,false),(179,true),(181,true)]
theorem inputList8330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) inputClause8330 (by decide) v hb
mask_input "8330|11972621413014756705924586149611790497021399392059392|3831428893049501329865950240769177098223247440937484288"
def inputClause8331 : CNF.NClause := [(155,true),(161,true),(167,false),(173,true),(179,true),(181,true)]
theorem inputList8331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) inputClause8331 (by decide) v hb
mask_input "8331|187072209578355573530071658587684226515959365500928|3843214442252937730998344755260201204493752880964042752"
def inputClause8336 : CNF.NClause := [(155,true),(160,true),(165,true),(170,false),(175,true),(180,true)]
theorem inputList8336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 30) (closed_mem 1 30) inputClause8336 (by decide) v hb
mask_input "8336|1496577676626844588240573268701473812127674924007424|1580434301743905971569062287213387005330317729773649920"
def inputClause8337 : CNF.NClause := [(155,true),(160,true),(165,false),(170,true),(175,true),(180,true)]
theorem inputList8337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 30) (closed_mem 1 30) inputClause8337 (by decide) v hb
mask_input "8337|46768052394588893382517914646921056628989841375232|1581884111368138227263920342567441558085816414856282112"
def inputClause8341 : CNF.NClause := [(211,true),(212,true),(213,true),(214,true),(215,false),(216,true)]
theorem inputList8341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 0) (closed_mem 2 0) inputClause8341 (by decide) v hb
mask_input "8341|52656145834278593348959013841835216159447547700274555627155488768|154677428388193367962567103160390947468377171369556507154769248256"
def inputClause8342 : CNF.NClause := [(211,true),(212,true),(213,true),(214,false),(215,true),(216,true)]
theorem inputList8342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 0) (closed_mem 2 0) inputClause8342 (by decide) v hb
mask_input "8342|26328072917139296674479506920917608079723773850137277813577744384|181005501305332664637046610081308555548100945219693784968346992640"
def inputClause8347 : CNF.NClause := [(190,true),(195,true),(200,true),(205,true),(210,false),(211,true)]
theorem inputList8347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 1) (closed_mem 2 1) inputClause8347 (by decide) v hb
mask_input "8347|1645504557321206042154969182557350504982735865633579863348609024|3344089856192275703519124759424700839096637274494408718546894848"
def inputClause8349 : CNF.NClause := [(190,true),(195,true),(200,false),(205,true),(210,true),(211,true)]
theorem inputList8349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 1) (closed_mem 2 1) inputClause8349 (by decide) v hb
mask_input "8349|1606938044258990275541962092341162602522202993782792835301376|4987987475469222755398551979889710181476850937134205789060202496"
def inputClause8357 : CNF.NClause := [(188,false),(193,true),(198,true),(203,true),(208,true),(211,true)]
theorem inputList8357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 2) (closed_mem 2 2) inputClause8357 (by decide) v hb
mask_input "8357|392318858461667547739736838950479151006397215279002157056|3715655047041321037983429519594699643014796077085151661494632448"
def inputClause8359 : CNF.NClause := [(189,true),(194,true),(199,true),(204,true),(209,false),(211,true)]
theorem inputList8359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 3) (closed_mem 2 3) inputClause8359 (by decide) v hb
mask_input "8359|822752278660603021077484591278675252491367932816789931674304512|3317549485417343893914531562269700924531054502880784222622056448"
def inputClause8363 : CNF.NClause := [(189,false),(194,true),(199,true),(204,true),(209,true),(211,true)]
theorem inputList8363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 3) (closed_mem 2 3) inputClause8363 (by decide) v hb
mask_input "8363|784637716923335095479473677900958302012794430558004314112|4140300979440229991656920674074698276064120422903143596292046848"
def inputClause8365 : CNF.NClause := [(187,true),(192,true),(197,true),(202,true),(207,false),(211,true)]
theorem inputList8365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) inputClause8365 (by decide) v hb
mask_input "8365|205688069665150755269371147819668813122841983204197482918576128|3297644207336145036711086664403450988606867424170565850678427648"
def inputClause8368 : CNF.NClause := [(187,true),(192,false),(197,true),(202,true),(207,true),(211,true)]
theorem inputList8368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) inputClause8368 (by decide) v hb
mask_input "8368|6277101735386680763835789423207666416102355444464034512896|3503325999899560405299693976433696594063293305019318869562490880"
def inputClause8373 : CNF.NClause := [(206,true),(207,true),(208,false),(209,true),(210,true),(216,true)]
theorem inputList8373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) inputClause8373 (by decide) v hb
mask_input "8373|411376139330301510538742295639337626245683966408394965837152256|108089080609036721894054538179235961296053462173805777273711755264"
def inputClause8374 : CNF.NClause := [(206,true),(207,false),(208,true),(209,true),(210,true),(216,true)]
theorem inputList8374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) inputClause8374 (by decide) v hb
mask_input "8374|205688069665150755269371147819668813122841983204197482918576128|108294768678701872649323909327055630109176304157009974756630331392"
def inputClause8375 : CNF.NClause := [(206,false),(207,true),(208,true),(209,true),(210,true),(216,true)]
theorem inputList8375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) inputClause8375 (by decide) v hb
mask_input "8375|102844034832575377634685573909834406561420991602098741459288064|108397612713534448026958594900965464515737725148612073498089619456"
def inputClause8378 : CNF.NClause := [(190,true),(194,true),(198,true),(202,false),(206,true),(215,true)]
theorem inputList8378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 6) (closed_mem 2 6) inputClause8378 (by decide) v hb
mask_input "8378|6427752177035961102167848369364650410088811975131171341205504|52759418281304608867555831208373184489241867677635739038970281984"
def inputClause8379 : CNF.NClause := [(190,true),(194,true),(198,false),(202,true),(206,true),(215,true)]
theorem inputList8379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 6) (closed_mem 2 6) inputClause8379 (by decide) v hb
mask_input "8379|401734511064747568885490523085290650630550748445698208825344|52765444298970580081089113566219463849001325938862424512102662144"
def inputClause8380 : CNF.NClause := [(190,true),(194,false),(198,true),(202,true),(206,true),(215,true)]
theorem inputList8380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 6) (closed_mem 2 6) inputClause8380 (by decide) v hb
mask_input "8380|25108406941546723055343157692830665664409421777856138051584|52765820925074703281934943713584856308986292080189092354173435904"
def inputClause8388 : CNF.NClause := [(189,true),(192,true),(200,true),(203,true),(206,true),(214,false)]
theorem inputList8388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 8) (closed_mem 2 8) inputClause8388 (by decide) v hb
mask_input "8388|26328072917139296674479506920917608079723773850137277813577744384|117313538970358600130422548004005978608838933696018899015827456"
def inputClause8390 : CNF.NClause := [(189,true),(192,true),(200,true),(203,false),(206,true),(214,true)]
theorem inputList8390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 8) (closed_mem 2 8) inputClause8390 (by decide) v hb
mask_input "8390|12855504354071922204335696738729300820177623950262342682411008|26432530951755583352405593772182884757512435159883034369911160832"
end Percolation.MaskChain
