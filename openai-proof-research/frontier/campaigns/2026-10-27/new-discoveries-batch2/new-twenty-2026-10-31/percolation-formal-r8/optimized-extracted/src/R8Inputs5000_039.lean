import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6056 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6056 (by decide) v hb
mask_input "6056|619158914302145660746465280|19343182048715540986396672"
def inputClause6057 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6057 (by decide) v hb
mask_input "6057|619121504305164177775853568|19380592045697023957008384"
def inputClause6058 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6058 (by decide) v hb
mask_input "6058|619121504305164177775788032|19380592045697023957073920"
def inputClause6059 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6059 (by decide) v hb
mask_input "6059|619121430518187882937647104|19380665832673318795214848"
def inputClause6060 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6060 (by decide) v hb
mask_input "6060|619121430518187882937581568|19380665832673318795280384"
def inputClause6061 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6061 (by decide) v hb
mask_input "6061|619121209157258998423027712|19380887193602203309834240"
def inputClause6063 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6063 (by decide) v hb
mask_input "6063|619121135370282703584821248|19380960980578498148040704"
def inputClause6064 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6064 (by decide) v hb
mask_input "6064|619121135370282703584755712|19380960980578498148106240"
def inputClause6065 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6065 (by decide) v hb
mask_input "6065|619008167509575306290724864|19493928841285895442137088"
def inputClause6066 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6066 (by decide) v hb
mask_input "6066|619008167509575306290659328|19493928841285895442202624"
def inputClause6067 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6067 (by decide) v hb
mask_input "6067|619008093722599011452518400|19494002628262190280343552"
def inputClause6068 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6068 (by decide) v hb
mask_input "6068|619008093722599011452452864|19494002628262190280409088"
def inputClause6069 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6069 (by decide) v hb
mask_input "6069|619007872361670126937899008|19494223989191074794962944"
def inputClause6071 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6071 (by decide) v hb
mask_input "6071|619007798574693832099692544|19494297776167369633169408"
def inputClause6072 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6072 (by decide) v hb
mask_input "6072|619007798574693832099627008|19494297776167369633234944"
def inputClause6073 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6073 (by decide) v hb
mask_input "6073|618970388577712349129015296|19531707773148852603846656"
def inputClause6074 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6074 (by decide) v hb
mask_input "6074|618970388577712349128949760|19531707773148852603912192"
def inputClause6075 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6075 (by decide) v hb
mask_input "6075|618970314790736054290808832|19531781560125147442053120"
def inputClause6076 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6076 (by decide) v hb
mask_input "6076|618970314790736054290743296|19531781560125147442118656"
def inputClause6077 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6077 (by decide) v hb
mask_input "6077|618970093429807169776189440|19532002921054031956672512"
def inputClause6079 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6079 (by decide) v hb
mask_input "6079|618970019642830874937982976|19532076708030326794878976"
def inputClause6080 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6080 (by decide) v hb
mask_input "6080|618970019642830874937917440|19532076708030326794944512"
def inputClause6081 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6081 (by decide) v hb
mask_input "6081|19532076708171064283299840|618970019642690137449562112"
def inputClause6082 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6082 (by decide) v hb
mask_input "6082|19532076708171064283234304|618970019642690137449627648"
def inputClause6083 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6083 (by decide) v hb
mask_input "6083|19532002921194769445093376|618970093429666432287768576"
def inputClause6084 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6084 (by decide) v hb
mask_input "6084|19532002921194769445027840|618970093429666432287834112"
def inputClause6085 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6085 (by decide) v hb
mask_input "6085|19531781560265884930473984|618970314790595316802387968"
def inputClause6087 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6087 (by decide) v hb
mask_input "6087|19531707773289590092267520|618970388577571611640594432"
def inputClause6088 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6088 (by decide) v hb
mask_input "6088|19531707773289590092201984|618970388577571611640659968"
def inputClause6089 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6089 (by decide) v hb
mask_input "6089|19494297776308107121590272|619007798574553094611271680"
def inputClause6090 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6090 (by decide) v hb
mask_input "6090|19494297776308107121524736|619007798574553094611337216"
def inputClause6091 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6091 (by decide) v hb
mask_input "6091|19494223989331812283383808|619007872361529389449478144"
def inputClause6092 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6092 (by decide) v hb
mask_input "6092|19494223989331812283318272|619007872361529389449543680"
def inputClause6093 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6093 (by decide) v hb
mask_input "6093|19494002628402927768764416|619008093722458273964097536"
def inputClause6095 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6095 (by decide) v hb
mask_input "6095|19493928841426632930557952|619008167509434568802304000"
def inputClause6096 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6096 (by decide) v hb
mask_input "6096|19493928841426632930492416|619008167509434568802369536"
def inputClause6097 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inputList6097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6097 (by decide) v hb
mask_input "6097|19380960980719235636461568|619121135370141966096400384"
def inputClause6098 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inputList6098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6098 (by decide) v hb
mask_input "6098|19380960980719235636396032|619121135370141966096465920"
def inputClause6099 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inputList6099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6099 (by decide) v hb
mask_input "6099|19380887193742940798255104|619121209157118260934606848"
def inputClause6100 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inputList6100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6100 (by decide) v hb
mask_input "6100|19380887193742940798189568|619121209157118260934672384"
end Percolation.MaskChain
