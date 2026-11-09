import NInputs115
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6590 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6590 (by decide) v hb
def cl_6591 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6591 (by decide) v hb
def cl_6592 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inp_6592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6592 (by decide) v hb
def cl_6593 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6593 (by decide) v hb
def cl_6594 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6594 (by decide) v hb
def cl_6595 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6595 (by decide) v hb
def cl_6596 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6596 (by decide) v hb
def cl_6597 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6597 (by decide) v hb
def cl_6598 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6598 (by decide) v hb
def cl_6599 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6599 (by decide) v hb
def cl_6600 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inp_6600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6600 (by decide) v hb
def cl_6601 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6601 (by decide) v hb
def cl_6602 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6602 (by decide) v hb
def cl_6603 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6603 (by decide) v hb
def cl_6604 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6604 (by decide) v hb
def cl_6605 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6605 (by decide) v hb
def cl_6606 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6606 (by decide) v hb
def cl_6607 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6607 (by decide) v hb
def cl_6608 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inp_6608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6608 (by decide) v hb
def cl_6609 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6609 (by decide) v hb
def cl_6610 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6610 (by decide) v hb
def cl_6611 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6611 (by decide) v hb
def cl_6612 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6612 (by decide) v hb
def cl_6613 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6613 (by decide) v hb
def cl_6614 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6614 (by decide) v hb
def cl_6615 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6615 (by decide) v hb
def cl_6616 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inp_6616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6616 (by decide) v hb
def cl_6617 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6617 (by decide) v hb
def cl_6618 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6618 (by decide) v hb
def cl_6619 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6619 (by decide) v hb
def cl_6620 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6620 (by decide) v hb
def cl_6621 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6621 (by decide) v hb
def cl_6622 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6622 (by decide) v hb
def cl_6623 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6623 (by decide) v hb
def cl_6624 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inp_6624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6624 (by decide) v hb
def cl_6625 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inp_6625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6625 (by decide) v hb
def cl_6626 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inp_6626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6626 (by decide) v hb
def cl_6627 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inp_6627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6627 (by decide) v hb
def cl_6628 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inp_6628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6628 (by decide) v hb
def cl_6630 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,true),(92,true)]
theorem inp_6630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6630 (by decide) v hb
def cl_6631 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,true),(92,true)]
theorem inp_6631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6631 (by decide) v hb
def cl_6632 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,true),(92,true)]
theorem inp_6632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6632 (by decide) v hb
def cl_6633 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inp_6633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6633 (by decide) v hb
def cl_6634 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inp_6634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6634 (by decide) v hb
def cl_6635 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inp_6635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6635 (by decide) v hb
def cl_6636 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inp_6636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6636 (by decide) v hb
def cl_6637 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,true),(92,true)]
theorem inp_6637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6637 (by decide) v hb
def cl_6638 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,true),(92,true)]
theorem inp_6638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6638 (by decide) v hb
def cl_6640 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,true),(92,true)]
theorem inp_6640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6640 (by decide) v hb
def cl_6641 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inp_6641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6641 (by decide) v hb
end Percolation.NReplay
