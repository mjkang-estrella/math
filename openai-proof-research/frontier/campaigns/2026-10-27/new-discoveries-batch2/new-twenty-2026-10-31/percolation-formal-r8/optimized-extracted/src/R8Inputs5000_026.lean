import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5480 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,true),(90,true)]
theorem inputList5480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5480 (by decide) v hb
mask_input "5480|1213648186101896866430976|1247612109925083961840633856"
def inputClause5481 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5481 (by decide) v hb
mask_input "5481|1209589902405680765077504|1247616168208780177941987328"
def inputClause5482 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5482 (by decide) v hb
mask_input "5482|1209589902405680765075456|1247616168208780177941989376"
def inputClause5483 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5483 (by decide) v hb
mask_input "5483|1209516115429385926871040|1247616241995756472780193792"
def inputClause5484 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5484 (by decide) v hb
mask_input "5484|1209516115429385926868992|1247616241995756472780195840"
def inputClause5485 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5485 (by decide) v hb
mask_input "5485|1208999606595322059425792|1247616758504590536647639040"
def inputClause5486 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5486 (by decide) v hb
mask_input "5486|1208999606595322059423744|1247616758504590536647641088"
def inputClause5487 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5487 (by decide) v hb
mask_input "5487|1208925819619027221219328|1247616832291566831485845504"
def inputClause5488 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inputList5488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5488 (by decide) v hb
mask_input "5488|1208925819619027221217280|1247616832291566831485847552"
def inputClause5489 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inputList5489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5489 (by decide) v hb
mask_input "5489|5386449273921235585024|1248820371661911937471479808"
def inputClause5490 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inputList5490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5490 (by decide) v hb
mask_input "5490|5386449273921235582976|1248820371661911937471481856"
def inputClause5491 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inputList5491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5491 (by decide) v hb
mask_input "5491|5312662297626397378560|1248820445448888232309686272"
def inputClause5492 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inputList5492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5492 (by decide) v hb
mask_input "5492|5312662297626397376512|1248820445448888232309688320"
def inputClause5493 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,true),(90,true)]
theorem inputList5493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5493 (by decide) v hb
mask_input "5493|4796153463562529933312|1248820961957722296177131520"
def inputClause5494 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,true),(90,true)]
theorem inputList5494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5494 (by decide) v hb
mask_input "5494|4796153463562529931264|1248820961957722296177133568"
def inputClause5497 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,true),(90,true)]
theorem inputList5497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5497 (by decide) v hb
mask_input "5497|664082791051590371328|1248825094028394807116693504"
def inputClause5498 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,true),(90,true)]
theorem inputList5498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5498 (by decide) v hb
mask_input "5498|664082791051590369280|1248825094028394807116695552"
def inputClause5500 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,true),(90,true)]
theorem inputList5500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5500 (by decide) v hb
mask_input "5500|590295814756752162816|1248825167815371101954902016"
def inputClause5501 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,true),(90,true)]
theorem inputList5501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5501 (by decide) v hb
mask_input "5501|73786980692884719616|1248825684324205165822345216"
def inputClause5502 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,true),(90,true)]
theorem inputList5502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5502 (by decide) v hb
mask_input "5502|73786980692884717568|1248825684324205165822347264"
def inputClause5504 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,true),(90,true)]
theorem inputList5504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5504 (by decide) v hb
mask_input "5504|4398046511104|1248825758111181460660553728"
def inputClause5505 : CNF.NClause := [(43,true),(12,false),(64,false),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5505 (by decide) v hb
mask_input "5505|2516988592398790064445853696|8796093022208"
def inputClause5506 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5506 (by decide) v hb
mask_input "5506|2516988592398798860538871808|4096"
def inputClause5507 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5507 (by decide) v hb
mask_input "5507|2516988573952054786829324288|18446744073709551616"
def inputClause5508 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5508 (by decide) v hb
mask_input "5508|2516988573952054786829320192|18446744073709555712"
def inputClause5509 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5509 (by decide) v hb
mask_input "5509|2516988297250893681186050048|295147905179352825856"
def inputClause5510 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5510 (by decide) v hb
mask_input "5510|2516988297250893681186045952|295147905179352829952"
def inputClause5511 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5511 (by decide) v hb
mask_input "5511|2516988278804149607476498432|313594649253062377472"
def inputClause5512 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inputList5512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5512 (by decide) v hb
mask_input "5512|2516988278804149607476494336|313594649253062381568"
def inputClause5513 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5513 (by decide) v hb
mask_input "5513|2516983870032315990893662208|4722366482869645213696"
def inputClause5514 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5514 (by decide) v hb
mask_input "5514|2516983870032315990893658112|4722366482869645217792"
def inputClause5515 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5515 (by decide) v hb
mask_input "5515|2516983851585571917184110592|4740813226943354765312"
def inputClause5516 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5516 (by decide) v hb
mask_input "5516|2516983851585571917184106496|4740813226943354769408"
def inputClause5517 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5517 (by decide) v hb
mask_input "5517|2516983574884410811540836352|5017514388048998039552"
def inputClause5518 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5518 (by decide) v hb
mask_input "5518|2516983574884410811540832256|5017514388048998043648"
def inputClause5519 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5519 (by decide) v hb
mask_input "5519|2516983556437666737831284736|5035961132122707591168"
def inputClause5520 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inputList5520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5520 (by decide) v hb
mask_input "5520|2516983556437666737831280640|5035961132122707595264"
def inputClause5521 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5521 (by decide) v hb
mask_input "5521|2514570740759569602189463552|2417851639229258349412352"
def inputClause5522 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5522 (by decide) v hb
mask_input "5522|2514570740759569602189459456|2417851639229258349416448"
def inputClause5523 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5523 (by decide) v hb
mask_input "5523|2514570722312825528479911936|2417870085973332058963968"
end Percolation.MaskChain
