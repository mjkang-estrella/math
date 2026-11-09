import NInputs114
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6540 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6540 (by decide) v hb
def cl_6541 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6541 (by decide) v hb
def cl_6542 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6542 (by decide) v hb
def cl_6543 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6543 (by decide) v hb
def cl_6544 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inp_6544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6544 (by decide) v hb
def cl_6545 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6545 (by decide) v hb
def cl_6546 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6546 (by decide) v hb
def cl_6547 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6547 (by decide) v hb
def cl_6548 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6548 (by decide) v hb
def cl_6549 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6549 (by decide) v hb
def cl_6550 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6550 (by decide) v hb
def cl_6551 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6551 (by decide) v hb
def cl_6552 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inp_6552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6552 (by decide) v hb
def cl_6553 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6553 (by decide) v hb
def cl_6554 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6554 (by decide) v hb
def cl_6555 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6555 (by decide) v hb
def cl_6556 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6556 (by decide) v hb
def cl_6557 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6557 (by decide) v hb
def cl_6558 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6558 (by decide) v hb
def cl_6559 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6559 (by decide) v hb
def cl_6560 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inp_6560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6560 (by decide) v hb
def cl_6561 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6561 (by decide) v hb
def cl_6562 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6562 (by decide) v hb
def cl_6563 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6563 (by decide) v hb
def cl_6564 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6564 (by decide) v hb
def cl_6565 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6565 (by decide) v hb
def cl_6566 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6566 (by decide) v hb
def cl_6567 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6567 (by decide) v hb
def cl_6568 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inp_6568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6568 (by decide) v hb
def cl_6569 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6569 (by decide) v hb
def cl_6570 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6570 (by decide) v hb
def cl_6571 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6571 (by decide) v hb
def cl_6572 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6572 (by decide) v hb
def cl_6573 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6573 (by decide) v hb
def cl_6574 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6574 (by decide) v hb
def cl_6575 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6575 (by decide) v hb
def cl_6576 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inp_6576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6576 (by decide) v hb
def cl_6577 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6577 (by decide) v hb
def cl_6578 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6578 (by decide) v hb
def cl_6579 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6579 (by decide) v hb
def cl_6580 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6580 (by decide) v hb
def cl_6581 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6581 (by decide) v hb
def cl_6582 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6582 (by decide) v hb
def cl_6583 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6583 (by decide) v hb
def cl_6584 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inp_6584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6584 (by decide) v hb
def cl_6585 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6585 (by decide) v hb
def cl_6586 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6586 (by decide) v hb
def cl_6587 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6587 (by decide) v hb
def cl_6588 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6588 (by decide) v hb
def cl_6589 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6589 (by decide) v hb
end Percolation.NReplay
