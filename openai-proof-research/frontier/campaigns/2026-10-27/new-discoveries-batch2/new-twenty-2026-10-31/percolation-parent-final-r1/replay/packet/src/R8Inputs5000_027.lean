import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5524 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5524 (by decide) v hb
mask_input "5524|2514570722312825528479907840|2417870085973332058968064"
def inputClause5525 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5525 (by decide) v hb
mask_input "5525|2514570445611664422836637696|2418146787134437702238208"
def inputClause5526 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5526 (by decide) v hb
mask_input "5526|2514570445611664422836633600|2418146787134437702242304"
def inputClause5527 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5527 (by decide) v hb
mask_input "5527|2514570427164920349127086080|2418165233878511411789824"
def inputClause5528 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inputList5528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5528 (by decide) v hb
mask_input "5528|2514570427164920349127081984|2418165233878511411793920"
def inputClause5529 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5529 (by decide) v hb
mask_input "5529|2514566018393086732544249856|2422574005712127994626048"
def inputClause5530 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5530 (by decide) v hb
mask_input "5530|2514566018393086732544245760|2422574005712127994630144"
def inputClause5531 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5531 (by decide) v hb
mask_input "5531|2514565999946342658834698240|2422592452456201704177664"
def inputClause5532 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5532 (by decide) v hb
mask_input "5532|2514565999946342658834694144|2422592452456201704181760"
def inputClause5533 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5533 (by decide) v hb
mask_input "5533|2514565723245181553191424000|2422869153617307347451904"
def inputClause5534 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5534 (by decide) v hb
mask_input "5534|2514565723245181553191419904|2422869153617307347456000"
def inputClause5535 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5535 (by decide) v hb
mask_input "5535|2514565704798437479481872384|2422887600361381057003520"
def inputClause5536 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inputList5536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5536 (by decide) v hb
mask_input "5536|2514565704798437479481868288|2422887600361381057007616"
def inputClause5537 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5537 (by decide) v hb
mask_input "5537|2478302966171130726948278272|38685626227668133590597632"
def inputClause5538 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5538 (by decide) v hb
mask_input "5538|2478302966171130726948274176|38685626227668133590601728"
def inputClause5539 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5539 (by decide) v hb
mask_input "5539|2478302947724386653238726656|38685644674412207300149248"
def inputClause5540 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5540 (by decide) v hb
mask_input "5540|2478302947724386653238722560|38685644674412207300153344"
def inputClause5541 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5541 (by decide) v hb
mask_input "5541|2478302671023225547595452416|38685921375573312943423488"
def inputClause5542 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5542 (by decide) v hb
mask_input "5542|2478302671023225547595448320|38685921375573312943427584"
def inputClause5543 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5543 (by decide) v hb
mask_input "5543|2478302652576481473885900800|38685939822317386652975104"
def inputClause5544 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inputList5544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5544 (by decide) v hb
mask_input "5544|2478302652576481473885896704|38685939822317386652979200"
def inputClause5545 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5545 (by decide) v hb
mask_input "5545|2478298243804647857303064576|38690348594151003235811328"
def inputClause5546 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5546 (by decide) v hb
mask_input "5546|2478298243804647857303060480|38690348594151003235815424"
def inputClause5547 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5547 (by decide) v hb
mask_input "5547|2478298225357903783593512960|38690367040895076945362944"
def inputClause5548 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5548 (by decide) v hb
mask_input "5548|2478298225357903783593508864|38690367040895076945367040"
def inputClause5549 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5549 (by decide) v hb
mask_input "5549|2478297948656742677950238720|38690643742056182588637184"
def inputClause5550 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5550 (by decide) v hb
mask_input "5550|2478297948656742677950234624|38690643742056182588641280"
def inputClause5551 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5551 (by decide) v hb
mask_input "5551|2478297930209998604240687104|38690662188800256298188800"
def inputClause5552 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inputList5552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5552 (by decide) v hb
mask_input "5552|2478297930209998604240683008|38690662188800256298192896"
def inputClause5553 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5553 (by decide) v hb
mask_input "5553|2475885114531901468598865920|41103477866897391940009984"
def inputClause5554 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5554 (by decide) v hb
mask_input "5554|2475885114531901468598861824|41103477866897391940014080"
def inputClause5555 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5555 (by decide) v hb
mask_input "5555|2475885096085157394889314304|41103496313641465649561600"
def inputClause5556 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5556 (by decide) v hb
mask_input "5556|2475885096085157394889310208|41103496313641465649565696"
def inputClause5557 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5557 (by decide) v hb
mask_input "5557|2475884819383996289246040064|41103773014802571292835840"
def inputClause5558 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5558 (by decide) v hb
mask_input "5558|2475884819383996289246035968|41103773014802571292839936"
def inputClause5559 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5559 (by decide) v hb
mask_input "5559|2475884800937252215536488448|41103791461546645002387456"
def inputClause5560 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inputList5560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5560 (by decide) v hb
mask_input "5560|2475884800937252215536484352|41103791461546645002391552"
def inputClause5561 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5561 (by decide) v hb
mask_input "5561|2475880392165418598953652224|41108200233380261585223680"
def inputClause5562 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5562 (by decide) v hb
mask_input "5562|2475880392165418598953648128|41108200233380261585227776"
def inputClause5563 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5563 (by decide) v hb
mask_input "5563|2475880373718674525244100608|41108218680124335294775296"
end Percolation.MaskChain
