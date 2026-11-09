import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause456 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,false),(27,false)]
theorem inputList456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause456 (by decide) v hb
mask_input "456|135528448|590295810358705654276"
def inputClause457 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,false),(27,false)]
theorem inputList457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause457 (by decide) v hb
mask_input "457|135268868|590295810358705913856"
def inputClause458 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,false),(27,false)]
theorem inputList458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause458 (by decide) v hb
mask_input "458|135268864|590295810358705913860"
def inputClause459 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,false),(27,false)]
theorem inputList459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause459 (by decide) v hb
mask_input "459|135268356|590295810358705914368"
def inputClause460 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,true),(20,false),(27,false)]
theorem inputList460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause460 (by decide) v hb
mask_input "460|135268352|590295810358705914372"
def inputClause461 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,false),(27,false)]
theorem inputList461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause461 (by decide) v hb
mask_input "461|135266820|590295810358705915904"
def inputClause462 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,true),(20,false),(27,false)]
theorem inputList462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause462 (by decide) v hb
mask_input "462|135266816|590295810358705915908"
def inputClause463 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,true),(20,false),(27,false)]
theorem inputList463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause463 (by decide) v hb
mask_input "463|135266308|590295810358705916416"
def inputClause464 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,true),(20,false),(27,false)]
theorem inputList464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause464 (by decide) v hb
mask_input "464|135266304|590295810358705916420"
def inputClause465 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,true),(27,false)]
theorem inputList465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause465 (by decide) v hb
mask_input "465|134482436|590295810358706700288"
def inputClause466 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,true),(27,false)]
theorem inputList466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause466 (by decide) v hb
mask_input "466|134482432|590295810358706700292"
def inputClause467 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,true),(27,false)]
theorem inputList467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause467 (by decide) v hb
mask_input "467|134481924|590295810358706700800"
def inputClause468 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,true),(27,false)]
theorem inputList468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause468 (by decide) v hb
mask_input "468|134481920|590295810358706700804"
def inputClause469 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,true),(27,false)]
theorem inputList469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause469 (by decide) v hb
mask_input "469|134480388|590295810358706702336"
def inputClause470 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,true),(27,false)]
theorem inputList470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause470 (by decide) v hb
mask_input "470|134480384|590295810358706702340"
def inputClause471 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,true),(27,false)]
theorem inputList471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause471 (by decide) v hb
mask_input "471|134479876|590295810358706702848"
def inputClause472 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,true),(27,false)]
theorem inputList472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause472 (by decide) v hb
mask_input "472|134479872|590295810358706702852"
def inputClause473 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,true),(27,false)]
theorem inputList473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause473 (by decide) v hb
mask_input "473|134220292|590295810358706962432"
def inputClause474 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,true),(27,false)]
theorem inputList474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause474 (by decide) v hb
mask_input "474|134220288|590295810358706962436"
def inputClause475 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,true),(27,false)]
theorem inputList475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause475 (by decide) v hb
mask_input "475|134219780|590295810358706962944"
def inputClause476 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,true),(20,true),(27,false)]
theorem inputList476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause476 (by decide) v hb
mask_input "476|134219776|590295810358706962948"
def inputClause477 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,true),(27,false)]
theorem inputList477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause477 (by decide) v hb
mask_input "477|134218244|590295810358706964480"
def inputClause478 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,true),(20,true),(27,false)]
theorem inputList478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause478 (by decide) v hb
mask_input "478|134218240|590295810358706964484"
def inputClause479 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,true),(20,true),(27,false)]
theorem inputList479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause479 (by decide) v hb
mask_input "479|134217732|590295810358706964992"
def inputClause481 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,false),(27,true)]
theorem inputList481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause481 (by decide) v hb
mask_input "481|1313284|590295810358839869440"
def inputClause482 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,false),(27,true)]
theorem inputList482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause482 (by decide) v hb
mask_input "482|1313280|590295810358839869444"
def inputClause483 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,false),(27,true)]
theorem inputList483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause483 (by decide) v hb
mask_input "483|1312772|590295810358839869952"
def inputClause484 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,false),(27,true)]
theorem inputList484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause484 (by decide) v hb
mask_input "484|1312768|590295810358839869956"
def inputClause485 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,false),(27,true)]
theorem inputList485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause485 (by decide) v hb
mask_input "485|1311236|590295810358839871488"
def inputClause486 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,false),(27,true)]
theorem inputList486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause486 (by decide) v hb
mask_input "486|1311232|590295810358839871492"
def inputClause487 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,false),(27,true)]
theorem inputList487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause487 (by decide) v hb
mask_input "487|1310724|590295810358839872000"
def inputClause488 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,false),(27,true)]
theorem inputList488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause488 (by decide) v hb
mask_input "488|1310720|590295810358839872004"
def inputClause489 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,false),(27,true)]
theorem inputList489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause489 (by decide) v hb
mask_input "489|1051140|590295810358840131584"
def inputClause490 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,false),(27,true)]
theorem inputList490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause490 (by decide) v hb
mask_input "490|1051136|590295810358840131588"
def inputClause491 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,false),(27,true)]
theorem inputList491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause491 (by decide) v hb
mask_input "491|1050628|590295810358840132096"
def inputClause492 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,true),(20,false),(27,true)]
theorem inputList492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause492 (by decide) v hb
mask_input "492|1050624|590295810358840132100"
def inputClause493 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,false),(27,true)]
theorem inputList493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause493 (by decide) v hb
mask_input "493|1049092|590295810358840133632"
def inputClause494 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,true),(20,false),(27,true)]
theorem inputList494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause494 (by decide) v hb
mask_input "494|1049088|590295810358840133636"
def inputClause495 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,true),(20,false),(27,true)]
theorem inputList495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause495 (by decide) v hb
mask_input "495|1048580|590295810358840134144"
def inputClause497 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,true),(27,true)]
theorem inputList497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause497 (by decide) v hb
mask_input "497|264708|590295810358840918016"
end Percolation.MaskChain
