import NInputs096
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5613 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inp_5613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5613 (by decide) v hb
def cl_5614 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inp_5614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5614 (by decide) v hb
def cl_5615 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inp_5615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5615 (by decide) v hb
def cl_5616 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inp_5616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5616 (by decide) v hb
def cl_5617 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5617 (by decide) v hb
def cl_5618 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5618 (by decide) v hb
def cl_5619 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5619 (by decide) v hb
def cl_5620 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5620 (by decide) v hb
def cl_5621 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5621 (by decide) v hb
def cl_5622 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5622 (by decide) v hb
def cl_5623 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5623 (by decide) v hb
def cl_5624 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inp_5624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5624 (by decide) v hb
def cl_5626 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,true),(91,true)]
theorem inp_5626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5626 (by decide) v hb
def cl_5628 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,true),(91,true)]
theorem inp_5628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5628 (by decide) v hb
def cl_5629 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,true),(91,true)]
theorem inp_5629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5629 (by decide) v hb
def cl_5630 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,true),(91,true)]
theorem inp_5630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5630 (by decide) v hb
def cl_5632 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,true),(91,true)]
theorem inp_5632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5632 (by decide) v hb
def cl_5633 : CNF.NClause := [(44,true),(13,false),(65,false),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5633 v hb
def cl_5634 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5634 (by decide) v hb
def cl_5635 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5635 (by decide) v hb
def cl_5636 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5636 (by decide) v hb
def cl_5637 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5637 (by decide) v hb
def cl_5638 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5638 (by decide) v hb
def cl_5639 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5639 (by decide) v hb
def cl_5640 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5640 (by decide) v hb
def cl_5641 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5641 (by decide) v hb
def cl_5642 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5642 v hb
def cl_5643 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5643 (by decide) v hb
def cl_5644 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5644 (by decide) v hb
def cl_5645 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5645 (by decide) v hb
def cl_5646 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5646 v hb
def cl_5647 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5647 (by decide) v hb
def cl_5648 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5648 (by decide) v hb
def cl_5649 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5649 (by decide) v hb
def cl_5650 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5650 (by decide) v hb
def cl_5651 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5651 (by decide) v hb
def cl_5652 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5652 (by decide) v hb
def cl_5653 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5653 (by decide) v hb
def cl_5654 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5654 (by decide) v hb
def cl_5655 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5655 (by decide) v hb
def cl_5656 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inp_5656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5656 (by decide) v hb
def cl_5657 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5657 (by decide) v hb
def cl_5658 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5658 (by decide) v hb
def cl_5659 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5659 (by decide) v hb
def cl_5660 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5660 (by decide) v hb
def cl_5661 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5661 (by decide) v hb
def cl_5662 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5662 (by decide) v hb
def cl_5663 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5663 (by decide) v hb
def cl_5664 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inp_5664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5664 (by decide) v hb
def cl_5665 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5665 (by decide) v hb
end Percolation.NReplay
