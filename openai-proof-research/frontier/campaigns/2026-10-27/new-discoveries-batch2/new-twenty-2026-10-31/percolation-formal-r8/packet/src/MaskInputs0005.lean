import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause411 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,true),(29,false)]
theorem inputList411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause411 (by decide) v hb
mask_input "411|536875024|295147905179353940224"
def inputClause412 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,true),(29,false)]
theorem inputList412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause412 (by decide) v hb
mask_input "412|536875008|295147905179353940240"
def inputClause413 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,true),(29,false)]
theorem inputList413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause413 (by decide) v hb
mask_input "413|536871184|295147905179353944064"
def inputClause414 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,true),(20,true),(29,false)]
theorem inputList414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause414 (by decide) v hb
mask_input "414|536871168|295147905179353944080"
def inputClause415 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,true),(29,false)]
theorem inputList415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause415 (by decide) v hb
mask_input "415|536870928|295147905179353944320"
def inputClause417 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,false),(29,true)]
theorem inputList417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause417 (by decide) v hb
mask_input "417|1118480|295147905179889696768"
def inputClause418 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,false),(29,true)]
theorem inputList418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause418 (by decide) v hb
mask_input "418|1118464|295147905179889696784"
def inputClause419 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,false),(29,true)]
theorem inputList419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause419 (by decide) v hb
mask_input "419|1118224|295147905179889697024"
def inputClause420 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,false),(29,true)]
theorem inputList420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause420 (by decide) v hb
mask_input "420|1118208|295147905179889697040"
def inputClause421 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,false),(29,true)]
theorem inputList421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause421 (by decide) v hb
mask_input "421|1114384|295147905179889700864"
def inputClause422 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,false),(29,true)]
theorem inputList422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause422 (by decide) v hb
mask_input "422|1114368|295147905179889700880"
def inputClause423 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,false),(29,true)]
theorem inputList423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause423 (by decide) v hb
mask_input "423|1114128|295147905179889701120"
def inputClause424 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,false),(29,true)]
theorem inputList424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause424 (by decide) v hb
mask_input "424|1114112|295147905179889701136"
def inputClause425 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,false),(29,true)]
theorem inputList425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause425 (by decide) v hb
mask_input "425|1052944|295147905179889762304"
def inputClause426 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,false),(29,true)]
theorem inputList426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause426 (by decide) v hb
mask_input "426|1052928|295147905179889762320"
def inputClause427 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,false),(29,true)]
theorem inputList427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause427 (by decide) v hb
mask_input "427|1052688|295147905179889762560"
def inputClause428 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,false),(29,true)]
theorem inputList428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause428 (by decide) v hb
mask_input "428|1052672|295147905179889762576"
def inputClause429 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,false),(29,true)]
theorem inputList429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause429 (by decide) v hb
mask_input "429|1048848|295147905179889766400"
def inputClause430 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,true),(20,false),(29,true)]
theorem inputList430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause430 (by decide) v hb
mask_input "430|1048832|295147905179889766416"
def inputClause431 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,false),(29,true)]
theorem inputList431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause431 (by decide) v hb
mask_input "431|1048592|295147905179889766656"
def inputClause433 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,true),(29,true)]
theorem inputList433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause433 (by decide) v hb
mask_input "433|69904|295147905179890745344"
def inputClause434 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,true),(29,true)]
theorem inputList434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause434 (by decide) v hb
mask_input "434|69888|295147905179890745360"
def inputClause435 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,true),(29,true)]
theorem inputList435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause435 (by decide) v hb
mask_input "435|69648|295147905179890745600"
def inputClause436 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,true),(29,true)]
theorem inputList436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause436 (by decide) v hb
mask_input "436|69632|295147905179890745616"
def inputClause437 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,true),(29,true)]
theorem inputList437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause437 (by decide) v hb
mask_input "437|65808|295147905179890749440"
def inputClause438 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,true),(29,true)]
theorem inputList438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause438 (by decide) v hb
mask_input "438|65792|295147905179890749456"
def inputClause439 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,true),(29,true)]
theorem inputList439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause439 (by decide) v hb
mask_input "439|65552|295147905179890749696"
def inputClause441 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,true),(29,true)]
theorem inputList441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause441 (by decide) v hb
mask_input "441|4368|295147905179890810880"
def inputClause442 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,true),(29,true)]
theorem inputList442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause442 (by decide) v hb
mask_input "442|4352|295147905179890810896"
def inputClause443 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,true),(29,true)]
theorem inputList443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause443 (by decide) v hb
mask_input "443|4112|295147905179890811136"
def inputClause445 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,true),(29,true)]
theorem inputList445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause445 (by decide) v hb
mask_input "445|272|295147905179890814976"
def inputClause447 : CNF.NClause := [(68,false),(4,false),(8,true),(12,true),(16,true),(20,true),(29,true)]
theorem inputList447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause447 (by decide) v hb
mask_input "447|295147905179352825872|537989376"
def inputClause448 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,true),(29,true)]
theorem inputList448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause448 (by decide) v hb
mask_input "448|295147905179352825856|537989392"
def inputClause449 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,false),(27,false)]
theorem inputList449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause449 (by decide) v hb
mask_input "449|135531012|590295810358705651712"
def inputClause450 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,false),(27,false)]
theorem inputList450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause450 (by decide) v hb
mask_input "450|135531008|590295810358705651716"
def inputClause451 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,false),(27,false)]
theorem inputList451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause451 (by decide) v hb
mask_input "451|135530500|590295810358705652224"
def inputClause452 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,false),(27,false)]
theorem inputList452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause452 (by decide) v hb
mask_input "452|135530496|590295810358705652228"
def inputClause453 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,false),(27,false)]
theorem inputList453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause453 (by decide) v hb
mask_input "453|135528964|590295810358705653760"
def inputClause454 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,false),(27,false)]
theorem inputList454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause454 (by decide) v hb
mask_input "454|135528960|590295810358705653764"
def inputClause455 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,false),(27,false)]
theorem inputList455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause455 (by decide) v hb
mask_input "455|135528452|590295810358705654272"
end Percolation.MaskChain
