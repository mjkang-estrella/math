import NInputs076
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4584 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4584 (by decide) v hb
def cl_4585 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4585 (by decide) v hb
def cl_4586 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4586 (by decide) v hb
def cl_4587 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4587 (by decide) v hb
def cl_4588 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4588 (by decide) v hb
def cl_4589 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4589 (by decide) v hb
def cl_4590 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4590 (by decide) v hb
def cl_4591 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4591 (by decide) v hb
def cl_4592 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inp_4592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4592 (by decide) v hb
def cl_4593 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4593 (by decide) v hb
def cl_4594 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4594 (by decide) v hb
def cl_4595 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4595 (by decide) v hb
def cl_4596 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4596 (by decide) v hb
def cl_4597 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4597 (by decide) v hb
def cl_4598 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4598 (by decide) v hb
def cl_4599 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4599 (by decide) v hb
def cl_4600 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inp_4600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4600 (by decide) v hb
def cl_4601 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4601 (by decide) v hb
def cl_4602 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4602 (by decide) v hb
def cl_4603 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4603 (by decide) v hb
def cl_4604 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4604 (by decide) v hb
def cl_4605 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4605 (by decide) v hb
def cl_4606 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4606 (by decide) v hb
def cl_4607 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4607 (by decide) v hb
def cl_4608 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inp_4608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4608 (by decide) v hb
def cl_4609 : CNF.NClause := [(36,true),(5,false),(82,false),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4609 (by decide) v hb
def cl_4610 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4610 (by decide) v hb
def cl_4611 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4611 (by decide) v hb
def cl_4612 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4612 v hb
def cl_4613 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4613 (by decide) v hb
def cl_4614 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4614 (by decide) v hb
def cl_4615 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4615 (by decide) v hb
def cl_4616 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4616 (by decide) v hb
def cl_4617 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4617 (by decide) v hb
def cl_4618 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4618 (by decide) v hb
def cl_4619 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4619 (by decide) v hb
def cl_4620 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4620 v hb
def cl_4621 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4621 (by decide) v hb
def cl_4622 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4622 (by decide) v hb
def cl_4623 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4623 (by decide) v hb
def cl_4624 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4624 (by decide) v hb
def cl_4625 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4625 (by decide) v hb
def cl_4626 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4626 v hb
def cl_4627 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4627 (by decide) v hb
def cl_4628 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4628 v hb
def cl_4629 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4629 (by decide) v hb
def cl_4630 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4630 v hb
def cl_4631 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4631 (by decide) v hb
def cl_4632 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4632 v hb
def cl_4633 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4633 (by decide) v hb
end Percolation.NReplay
