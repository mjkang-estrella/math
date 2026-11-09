import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8055 : CNF.NClause := [(125,true),(132,true),(134,false),(141,true),(148,true),(151,true)]
theorem inputList8055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) inputClause8055 (by decide) v hb
mask_input "8055|21778071482940061661655974875633165533184|3214100388791392660406558742960989939311837184"
def inputClause8064 : CNF.NClause := [(128,true),(130,true),(137,true),(139,true),(146,true),(151,false)]
theorem inputList8064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) inputClause8064 (by decide) v hb
mask_input "8064|2854495385411919762116571938898990272765493248|90075805065274699724926428958655931486306304"
def inputClause8067 : CNF.NClause := [(128,true),(130,true),(137,false),(139,true),(146,true),(151,true)]
theorem inputList8067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) inputClause8067 (by decide) v hb
mask_input "8067|174224571863520493293247799005065324265472|2944396965905330941348205120058641138927534080"
def inputClause8068 : CNF.NClause := [(128,true),(130,false),(137,true),(139,true),(146,true),(151,true)]
theorem inputList8068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) inputClause8068 (by decide) v hb
mask_input "8068|1361129467683753853853498429727072845824|2944569829347726778087644514359216477178953728"
def inputClause8070 : CNF.NClause := [(126,true),(132,true),(138,true),(139,true),(145,true),(150,false)]
theorem inputList8070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) inputClause8070 (by decide) v hb
mask_input "8070|1427247692705959881058285969449495136382746624|45652367416704834492862203176697881190989824"
def inputClause8071 : CNF.NClause := [(126,true),(132,true),(138,true),(139,true),(145,false),(150,true)]
theorem inputList8071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) inputClause8071 (by decide) v hb
mask_input "8071|44601490397061246283071436545296723011960832|1428298569725603469268076736080896294561775616"
def inputClause8073 : CNF.NClause := [(126,true),(132,true),(138,false),(139,true),(145,true),(150,true)]
theorem inputList8073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) inputClause8073 (by decide) v hb
mask_input "8073|348449143727040986586495598010130648530944|1472551610978937674564561677028182886925205504"
def inputClause8074 : CNF.NClause := [(126,true),(132,false),(138,true),(139,true),(145,true),(150,true)]
theorem inputList8074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) inputClause8074 (by decide) v hb
mask_input "8074|5444517870735015415413993718908291383296|1472894615604793980535732758632474109282353152"
def inputClause8075 : CNF.NClause := [(126,false),(132,true),(138,true),(139,true),(145,true),(150,true)]
theorem inputList8075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) inputClause8075 (by decide) v hb
mask_input "8075|85070591730234615865843651857942052864|1472899975052072985316532306782541159631683584"
def inputClause8076 : CNF.NClause := [(127,true),(131,true),(135,true),(139,true),(148,true),(153,false)]
theorem inputList8076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) inputClause8076 (by decide) v hb
mask_input "8076|11417981541647679048466287755595961091061972992|357555270007028760338007234192308481753612288"
def inputClause8077 : CNF.NClause := [(127,true),(131,true),(135,true),(139,true),(148,false),(153,true)]
theorem inputList8077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) inputClause8077 (by decide) v hb
mask_input "8077|356811923176489970264571492362373784095686656|11418724888478217838539723497425895788719898624"
def inputClause8082 : CNF.NClause := [(125,true),(133,true),(136,true),(139,true),(147,true),(152,false)]
theorem inputList8082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) inputClause8082 (by decide) v hb
mask_input "8082|5708990770823839524233143877797980545530986496|179200903732668162500244122185973431560830976"
def inputClause8084 : CNF.NClause := [(125,true),(133,true),(136,true),(139,false),(147,true),(152,true)]
theorem inputList8084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) inputClause8084 (by decide) v hb
mask_input "8084|696898287454081973172991196020261297061888|5887494776269053604760215008787933715794755584"
def inputClause8085 : CNF.NClause := [(125,true),(133,true),(136,false),(139,true),(147,true),(152,true)]
theorem inputList8085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) inputClause8085 (by decide) v hb
mask_input "8085|87112285931760246646623899502532662132736|5888104562270575926486741376084451444429684736"
def inputClause8086 : CNF.NClause := [(125,true),(133,false),(136,true),(139,true),(147,true),(152,true)]
theorem inputList8086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) inputClause8086 (by decide) v hb
mask_input "8086|10889035741470030830827987437816582766592|5888180785520766216702557171996516160509050880"
def inputClause8087 : CNF.NClause := [(125,false),(133,true),(136,true),(139,true),(147,true),(152,true)]
theorem inputList8087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) inputClause8087 (by decide) v hb
mask_input "8087|42535295865117307932921825928971026432|5888191632021211821616080067062128048120791040"
def inputClause8096 : CNF.NClause := [(128,true),(129,true),(135,true),(141,false),(147,true),(150,true)]
theorem inputList8096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) inputClause8096 (by decide) v hb
mask_input "8096|2787593149816327892691964784081045188247552|1605698231284271509129285417704255590066290688"
def inputClause8097 : CNF.NClause := [(128,true),(129,true),(135,false),(141,true),(147,true),(150,true)]
theorem inputList8097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) inputClause8097 (by decide) v hb
mask_input "8097|43556142965880123323311949751266331066368|1608442268291121956898654070538585368923471872"
def inputClause8098 : CNF.NClause := [(128,true),(129,false),(135,true),(141,true),(147,true),(150,true)]
theorem inputList8098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) inputClause8098 (by decide) v hb
mask_input "8098|680564733841876926926749214863536422912|1608485143869353995145050455739121771718115328"
def inputClause8105 : CNF.NClause := [(126,false),(129,true),(137,true),(140,true),(148,true),(152,true)]
theorem inputList8105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) inputClause8105 (by decide) v hb
mask_input "8105|85070591730234615865843651857942052864|6067371395711835020814281527100614781081485312"
def inputClause8106 : CNF.NClause := [(127,true),(129,true),(136,true),(143,true),(145,true),(151,false)]
theorem inputList8106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) inputClause8106 (by decide) v hb
mask_input "8106|2854495385411919762116571938898990272765493248|55839825988175620446644578017642015847612416"
def inputClause8108 : CNF.NClause := [(127,true),(129,true),(136,true),(143,false),(145,true),(151,true)]
theorem inputList8108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) inputClause8108 (by decide) v hb
mask_input "8108|11150372599265311570767859136324180752990208|2899184838800830070992448657780308107860115456"
def inputClause8109 : CNF.NClause := [(127,true),(129,true),(136,false),(143,true),(145,true),(151,true)]
theorem inputList8109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) inputClause8109 (by decide) v hb
mask_input "8109|87112285931760246646623899502532662132736|2910248099114163622316569893017129755950972928"
def inputClause8111 : CNF.NClause := [(127,false),(129,true),(136,true),(143,true),(145,true),(151,true)]
theorem inputList8111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) inputClause8111 (by decide) v hb
mask_input "8111|170141183460469231731687303715884105728|2910335041258911922093984785229328572728999936"
def inputClause8113 : CNF.NClause := [(125,true),(129,true),(138,true),(142,true),(146,false),(153,true)]
theorem inputList8113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) inputClause8113 (by decide) v hb
mask_input "8113|89202980794122492566142873090593446023921664|11423905900191068452232493040433174104594448384"
def inputClause8115 : CNF.NClause := [(125,true),(129,true),(138,false),(142,true),(146,true),(153,true)]
theorem inputList8115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) inputClause8115 (by decide) v hb
mask_input "8115|348449143727040986586495598010130648530944|11512760431841463903812049417925757419969839104"
def inputClause8249 : CNF.NClause := [(170,false),(171,true),(172,true),(173,true),(174,true),(185,true)]
theorem inputList8249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 15) (closed_mem 1 15) inputClause8249 (by decide) v hb
mask_input "8249|1496577676626844588240573268701473812127674924007424|49084754638007248805114322066870938090163482157595492352"
def inputClause8303 : CNF.NClause := [(156,false),(160,true),(169,true),(173,true),(177,true),(184,true)]
theorem inputList8303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 24) (closed_mem 1 24) inputClause8303 (by decide) v hb
mask_input "8303|91343852333181432387730302044767688728495783936|24724212968215423350931308889267530829538273237997191168"
def inputClause8527 : CNF.NClause := [(242,true),(243,true),(244,true),(245,true),(246,false),(247,true)]
theorem inputList8527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) inputClause8527 (by decide) v hb
mask_input "8527|113078212145816597093331040047546785012958969400039613319782796882727665664|332167248178336253961659930139668680975566972612616364126861965843012517888"
def inputClause8528 : CNF.NClause := [(242,true),(243,true),(244,true),(245,false),(246,true),(247,true)]
theorem inputList8528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) inputClause8528 (by decide) v hb
mask_input "8528|56539106072908298546665520023773392506479484700019806659891398441363832832|388706354251244552508325450163442073482046457312636170786753364284376350720"
def inputClause8529 : CNF.NClause := [(242,true),(243,true),(244,false),(245,true),(246,true),(247,true)]
theorem inputList8529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) inputClause8529 (by decide) v hb
mask_input "8529|28269553036454149273332760011886696253239742350009903329945699220681916416|416975907287698701781658210175328769735286199662646074116699063505058267136"
def inputClause8530 : CNF.NClause := [(242,true),(243,false),(244,true),(245,true),(246,true),(247,true)]
theorem inputList8530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) inputClause8530 (by decide) v hb
mask_input "8530|14134776518227074636666380005943348126619871175004951664972849610340958208|431110683805925776418324590181272117861906070837651025781671913115399225344"
def inputClause8534 : CNF.NClause := [(221,true),(226,true),(231,true),(236,false),(241,true),(242,true)]
theorem inputList8534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) inputClause8534 (by decide) v hb
mask_input "8534|110427941548649020598956093796432407239217743554726184882600387580788736|10604644471623703255782655383825883563667657688960541921868703022259896320"
def inputClause8543 : CNF.NClause := [(219,false),(224,true),(229,true),(234,true),(239,true),(242,true)]
theorem inputList8543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) inputClause8543 (by decide) v hb
mask_input "8543|842498333348457493583344221469363458551160763204392890034487820288|7979308455129907709387801788290113070845711997594910696659754421850210304"
def inputClause8549 : CNF.NClause := [(220,false),(225,true),(230,true),(235,true),(240,true),(242,true)]
theorem inputList8549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 3) (closed_mem 3 3) inputClause8549 (by decide) v hb
mask_input "8549|1684996666696914987166688442938726917102321526408785780068975640576|8891228651146278100442413573608552078381488407687345560833084038529941504"
def inputClause8553 : CNF.NClause := [(218,true),(223,true),(228,false),(233,true),(238,true),(242,true)]
theorem inputList8553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) inputClause8553 (by decide) v hb
mask_input "8553|431359146674410236714672241392314090778194310760649159697657763987456|7522917419224214777852528015061611987668774873818314217609836972990267392"
def inputClause8555 : CNF.NClause := [(218,false),(223,true),(228,true),(233,true),(238,true),(242,true)]
theorem inputList8555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) inputClause8555 (by decide) v hb
mask_input "8555|421249166674228746791672110734681729275580381602196445017243910144|7523348357121722513860495895630893567077823792548693264573089613510344704"
def inputClause8557 : CNF.NClause := [(237,true),(238,true),(239,true),(240,true),(241,false),(247,true)]
theorem inputList8557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) inputClause8557 (by decide) v hb
mask_input "8557|3533694129556768659166595001485837031654967793751237916243212402585239552|229469262538092664804630762908986542243094471106721012186043605392878993408"
def inputClause8558 : CNF.NClause := [(237,true),(238,true),(239,true),(240,false),(241,true),(247,true)]
theorem inputList8558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) inputClause8558 (by decide) v hb
mask_input "8558|1766847064778384329583297500742918515827483896875618958121606201292619776|231236109602871049134214060409729460758921955003596631144165211594171613184"
def inputClause8559 : CNF.NClause := [(237,true),(238,true),(239,false),(240,true),(241,true),(247,true)]
theorem inputList8559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) inputClause8559 (by decide) v hb
mask_input "8559|883423532389192164791648750371459257913741948437809479060803100646309888|232119533135260241299005709160100920016835696952034440623226014694817923072"
end Percolation.MaskChain
