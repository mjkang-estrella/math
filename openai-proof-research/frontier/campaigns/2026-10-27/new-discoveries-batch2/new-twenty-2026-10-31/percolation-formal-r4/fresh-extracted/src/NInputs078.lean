import NInputs077
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4634 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4634 v hb
def cl_4635 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4635 (by decide) v hb
def cl_4636 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4636 (by decide) v hb
def cl_4637 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4637 (by decide) v hb
def cl_4638 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4638 v hb
def cl_4639 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4639 (by decide) v hb
def cl_4640 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4640 (by decide) v hb
def cl_4641 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4641 (by decide) v hb
def cl_4642 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4642 (by decide) v hb
def cl_4643 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4643 (by decide) v hb
def cl_4644 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4644 (by decide) v hb
def cl_4645 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4645 (by decide) v hb
def cl_4646 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4646 (by decide) v hb
def cl_4647 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4647 (by decide) v hb
def cl_4648 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inp_4648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4648 (by decide) v hb
def cl_4649 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4649 (by decide) v hb
def cl_4650 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4650 (by decide) v hb
def cl_4651 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4651 (by decide) v hb
def cl_4652 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4652 (by decide) v hb
def cl_4653 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4653 (by decide) v hb
def cl_4654 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4654 (by decide) v hb
def cl_4655 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4655 (by decide) v hb
def cl_4656 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inp_4656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4656 (by decide) v hb
def cl_4657 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4657 (by decide) v hb
def cl_4658 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4658 (by decide) v hb
def cl_4659 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4659 (by decide) v hb
def cl_4660 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4660 (by decide) v hb
def cl_4661 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4661 (by decide) v hb
def cl_4662 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4662 (by decide) v hb
def cl_4663 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4663 (by decide) v hb
def cl_4664 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inp_4664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4664 (by decide) v hb
def cl_4665 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4665 (by decide) v hb
def cl_4666 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4666 (by decide) v hb
def cl_4667 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4667 (by decide) v hb
def cl_4668 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4668 (by decide) v hb
def cl_4669 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4669 (by decide) v hb
def cl_4670 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4670 (by decide) v hb
def cl_4671 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4671 (by decide) v hb
def cl_4672 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inp_4672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4672 (by decide) v hb
def cl_4673 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4673 (by decide) v hb
def cl_4674 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4674 (by decide) v hb
def cl_4675 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4675 (by decide) v hb
def cl_4676 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4676 (by decide) v hb
def cl_4677 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4677 (by decide) v hb
def cl_4678 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4678 (by decide) v hb
def cl_4679 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4679 (by decide) v hb
def cl_4680 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inp_4680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4680 (by decide) v hb
def cl_4681 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4681 (by decide) v hb
def cl_4682 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4682 (by decide) v hb
def cl_4683 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4683 (by decide) v hb
end Percolation.NReplay
