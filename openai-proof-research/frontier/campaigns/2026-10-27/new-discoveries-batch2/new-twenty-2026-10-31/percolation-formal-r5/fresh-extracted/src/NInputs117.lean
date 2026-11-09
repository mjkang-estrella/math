import NInputs116
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6642 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inp_6642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6642 (by decide) v hb
def cl_6643 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inp_6643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6643 (by decide) v hb
def cl_6644 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inp_6644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6644 (by decide) v hb
def cl_6646 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,true),(92,true)]
theorem inp_6646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6646 (by decide) v hb
def cl_6648 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,true),(92,true)]
theorem inp_6648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6648 (by decide) v hb
def cl_6649 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6649 (by decide) v hb
def cl_6650 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6650 (by decide) v hb
def cl_6651 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6651 (by decide) v hb
def cl_6652 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6652 (by decide) v hb
def cl_6653 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6653 (by decide) v hb
def cl_6654 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6654 (by decide) v hb
def cl_6655 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6655 (by decide) v hb
def cl_6656 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inp_6656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6656 (by decide) v hb
def cl_6657 : CNF.NClause := [(52,true),(21,false),(66,false),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6657 (by decide) v hb
def cl_6658 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6658 v hb
def cl_6659 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6659 (by decide) v hb
def cl_6660 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6660 (by decide) v hb
def cl_6661 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6661 (by decide) v hb
def cl_6662 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6662 (by decide) v hb
def cl_6663 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6663 (by decide) v hb
def cl_6664 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6664 (by decide) v hb
def cl_6665 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6665 (by decide) v hb
def cl_6666 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6666 v hb
def cl_6667 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6667 (by decide) v hb
def cl_6668 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6668 (by decide) v hb
def cl_6669 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6669 (by decide) v hb
def cl_6670 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6670 (by decide) v hb
def cl_6671 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6671 (by decide) v hb
def cl_6672 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6672 (by decide) v hb
def cl_6673 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6673 (by decide) v hb
def cl_6674 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6674 v hb
def cl_6675 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6675 (by decide) v hb
def cl_6676 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6676 (by decide) v hb
def cl_6677 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6677 (by decide) v hb
def cl_6678 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6678 (by decide) v hb
def cl_6679 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6679 (by decide) v hb
def cl_6680 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6680 (by decide) v hb
def cl_6681 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6681 (by decide) v hb
def cl_6682 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6682 v hb
def cl_6683 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6683 (by decide) v hb
def cl_6684 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6684 (by decide) v hb
def cl_6685 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6685 (by decide) v hb
def cl_6686 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6686 (by decide) v hb
def cl_6687 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6687 (by decide) v hb
def cl_6688 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6688 (by decide) v hb
def cl_6689 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6689 (by decide) v hb
def cl_6690 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6690 v hb
def cl_6691 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6691 (by decide) v hb
def cl_6692 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6692 (by decide) v hb
def cl_6693 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6693 (by decide) v hb
end Percolation.NReplay
