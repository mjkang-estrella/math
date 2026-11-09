import NInputs113
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6487 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6487 (by decide) v hb
def cl_6488 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6488 (by decide) v hb
def cl_6489 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6489 (by decide) v hb
def cl_6490 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6490 (by decide) v hb
def cl_6491 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6491 (by decide) v hb
def cl_6492 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6492 (by decide) v hb
def cl_6493 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6493 (by decide) v hb
def cl_6494 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6494 (by decide) v hb
def cl_6495 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6495 (by decide) v hb
def cl_6496 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inp_6496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6496 (by decide) v hb
def cl_6497 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6497 (by decide) v hb
def cl_6498 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6498 (by decide) v hb
def cl_6499 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6499 (by decide) v hb
def cl_6500 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6500 (by decide) v hb
def cl_6501 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6501 (by decide) v hb
def cl_6502 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6502 (by decide) v hb
def cl_6503 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6503 (by decide) v hb
def cl_6504 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inp_6504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6504 (by decide) v hb
def cl_6505 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6505 (by decide) v hb
def cl_6506 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6506 (by decide) v hb
def cl_6507 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6507 (by decide) v hb
def cl_6508 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6508 (by decide) v hb
def cl_6509 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6509 (by decide) v hb
def cl_6510 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6510 (by decide) v hb
def cl_6511 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6511 (by decide) v hb
def cl_6512 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inp_6512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6512 (by decide) v hb
def cl_6514 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,true),(90,true)]
theorem inp_6514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6514 (by decide) v hb
def cl_6515 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,true),(90,true)]
theorem inp_6515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6515 (by decide) v hb
def cl_6516 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,true),(90,true)]
theorem inp_6516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6516 (by decide) v hb
def cl_6517 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inp_6517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6517 (by decide) v hb
def cl_6518 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inp_6518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6518 (by decide) v hb
def cl_6519 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inp_6519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6519 (by decide) v hb
def cl_6520 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inp_6520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6520 (by decide) v hb
def cl_6521 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inp_6521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6521 (by decide) v hb
def cl_6522 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inp_6522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6522 (by decide) v hb
def cl_6523 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inp_6523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6523 (by decide) v hb
def cl_6524 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inp_6524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6524 (by decide) v hb
def cl_6526 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,true),(90,true)]
theorem inp_6526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6526 (by decide) v hb
def cl_6528 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,true),(90,true)]
theorem inp_6528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6528 (by decide) v hb
def cl_6529 : CNF.NClause := [(51,true),(20,false),(67,false),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6529 (by decide) v hb
def cl_6530 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6530 (by decide) v hb
def cl_6531 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6531 (by decide) v hb
def cl_6532 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6532 (by decide) v hb
def cl_6533 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6533 v hb
def cl_6534 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6534 v hb
def cl_6535 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6535 (by decide) v hb
def cl_6536 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6536 (by decide) v hb
def cl_6537 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6537 (by decide) v hb
def cl_6538 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6538 (by decide) v hb
def cl_6539 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6539 (by decide) v hb
end Percolation.NReplay
