import NInputs095
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5562 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5562 (by decide) v hb
def cl_5563 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5563 (by decide) v hb
def cl_5564 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5564 (by decide) v hb
def cl_5565 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5565 (by decide) v hb
def cl_5566 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5566 (by decide) v hb
def cl_5567 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5567 (by decide) v hb
def cl_5568 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5568 (by decide) v hb
def cl_5569 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5569 (by decide) v hb
def cl_5570 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5570 (by decide) v hb
def cl_5571 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5571 (by decide) v hb
def cl_5572 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5572 (by decide) v hb
def cl_5573 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5573 (by decide) v hb
def cl_5574 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5574 (by decide) v hb
def cl_5575 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5575 (by decide) v hb
def cl_5576 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inp_5576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5576 (by decide) v hb
def cl_5577 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5577 (by decide) v hb
def cl_5578 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5578 (by decide) v hb
def cl_5579 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5579 (by decide) v hb
def cl_5580 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5580 (by decide) v hb
def cl_5581 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5581 (by decide) v hb
def cl_5582 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5582 (by decide) v hb
def cl_5583 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5583 (by decide) v hb
def cl_5584 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inp_5584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5584 (by decide) v hb
def cl_5585 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5585 (by decide) v hb
def cl_5586 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5586 (by decide) v hb
def cl_5587 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5587 (by decide) v hb
def cl_5588 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5588 (by decide) v hb
def cl_5589 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5589 (by decide) v hb
def cl_5590 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5590 (by decide) v hb
def cl_5591 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5591 (by decide) v hb
def cl_5592 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inp_5592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5592 (by decide) v hb
def cl_5593 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5593 (by decide) v hb
def cl_5594 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5594 (by decide) v hb
def cl_5595 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5595 (by decide) v hb
def cl_5596 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5596 (by decide) v hb
def cl_5597 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5597 (by decide) v hb
def cl_5598 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5598 (by decide) v hb
def cl_5599 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5599 (by decide) v hb
def cl_5600 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inp_5600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5600 (by decide) v hb
def cl_5601 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5601 (by decide) v hb
def cl_5602 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5602 (by decide) v hb
def cl_5603 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5603 (by decide) v hb
def cl_5604 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5604 (by decide) v hb
def cl_5605 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5605 (by decide) v hb
def cl_5606 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5606 (by decide) v hb
def cl_5607 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5607 (by decide) v hb
def cl_5608 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inp_5608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5608 (by decide) v hb
def cl_5609 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,true),(91,true)]
theorem inp_5609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5609 (by decide) v hb
def cl_5610 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,true),(91,true)]
theorem inp_5610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5610 (by decide) v hb
def cl_5612 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,true),(91,true)]
theorem inp_5612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5612 (by decide) v hb
end Percolation.NReplay
