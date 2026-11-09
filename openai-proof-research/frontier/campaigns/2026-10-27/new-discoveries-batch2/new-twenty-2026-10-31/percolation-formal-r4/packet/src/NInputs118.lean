import NInputs117
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6694 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6694 (by decide) v hb
def cl_6695 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6695 (by decide) v hb
def cl_6696 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6696 (by decide) v hb
def cl_6697 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6697 (by decide) v hb
def cl_6698 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6698 v hb
def cl_6699 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6699 (by decide) v hb
def cl_6700 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6700 (by decide) v hb
def cl_6702 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6702 (by decide) v hb
def cl_6703 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6703 (by decide) v hb
def cl_6704 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6704 (by decide) v hb
def cl_6705 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inp_6705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6705 (by decide) v hb
def cl_6706 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inp_6706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6706 v hb
def cl_6707 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inp_6707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6707 (by decide) v hb
def cl_6708 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inp_6708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6708 (by decide) v hb
def cl_6710 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,true),(88,false)]
theorem inp_6710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6710 (by decide) v hb
def cl_6712 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,true),(88,false)]
theorem inp_6712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6712 (by decide) v hb
def cl_6713 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inp_6713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6713 (by decide) v hb
def cl_6714 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inp_6714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6714 (by decide) v hb
def cl_6715 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inp_6715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6715 (by decide) v hb
def cl_6716 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inp_6716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6716 (by decide) v hb
def cl_6718 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,true),(88,false)]
theorem inp_6718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6718 (by decide) v hb
def cl_6720 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,true),(88,false)]
theorem inp_6720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6720 (by decide) v hb
def cl_6721 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6721 (by decide) v hb
def cl_6722 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6722 v hb
def cl_6723 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6723 (by decide) v hb
def cl_6724 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6724 (by decide) v hb
def cl_6725 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6725 (by decide) v hb
def cl_6726 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6726 (by decide) v hb
def cl_6727 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6727 (by decide) v hb
def cl_6728 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6728 (by decide) v hb
def cl_6729 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6729 (by decide) v hb
def cl_6730 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6730 v hb
def cl_6731 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6731 (by decide) v hb
def cl_6732 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6732 (by decide) v hb
def cl_6733 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6733 (by decide) v hb
def cl_6734 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6734 (by decide) v hb
def cl_6735 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6735 (by decide) v hb
def cl_6736 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6736 (by decide) v hb
def cl_6737 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6737 (by decide) v hb
def cl_6738 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6738 v hb
def cl_6739 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6739 (by decide) v hb
def cl_6740 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6740 (by decide) v hb
def cl_6741 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6741 (by decide) v hb
def cl_6742 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6742 (by decide) v hb
def cl_6744 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6744 (by decide) v hb
def cl_6745 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6745 (by decide) v hb
def cl_6746 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6746 v hb
def cl_6747 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6747 (by decide) v hb
def cl_6748 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6748 (by decide) v hb
def cl_6750 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6750 (by decide) v hb
end Percolation.NReplay
