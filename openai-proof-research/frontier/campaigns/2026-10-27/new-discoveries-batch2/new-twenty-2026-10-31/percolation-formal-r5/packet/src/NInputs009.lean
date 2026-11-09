import NInputs008
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_694 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,true),(30,true)]
theorem inp_694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_694 (by decide) v hb
def cl_695 : CNF.NClause := [(72,true),(10,false),(11,true),(12,true),(13,false),(14,true),(30,true)]
theorem inp_695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_695 (by decide) v hb
def cl_696 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,false),(14,true),(30,true)]
theorem inp_696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_696 v hb
def cl_697 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,true),(14,true),(30,true)]
theorem inp_697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_697 v hb
def cl_698 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,true),(30,true)]
theorem inp_698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_698 v hb
def cl_699 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,true),(14,true),(30,true)]
theorem inp_699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_699 (by decide) v hb
def cl_700 : CNF.NClause := [(72,false),(10,true),(11,true),(12,false),(13,true),(14,true),(30,true)]
theorem inp_700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_700 v hb
def cl_701 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,true),(30,true)]
theorem inp_701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_701 v hb
def cl_702 : CNF.NClause := [(72,false),(10,true),(11,false),(12,true),(13,true),(14,true),(30,true)]
theorem inp_702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_702 v hb
def cl_703 : CNF.NClause := [(72,false),(10,false),(11,true),(12,true),(13,true),(14,true),(30,true)]
theorem inp_703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_703 v hb
def cl_704 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,true),(14,true),(30,true)]
theorem inp_704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_704 v hb
def cl_705 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,false),(28,false)]
theorem inp_705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_705 v hb
def cl_706 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,false),(28,false)]
theorem inp_706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_706 v hb
def cl_707 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,false),(28,false)]
theorem inp_707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_707 v hb
def cl_708 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,false),(28,false)]
theorem inp_708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_708 v hb
def cl_709 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,false),(28,false)]
theorem inp_709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_709 v hb
def cl_710 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,false),(28,false)]
theorem inp_710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_710 v hb
def cl_711 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,false),(28,false)]
theorem inp_711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_711 v hb
def cl_712 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,false),(28,false)]
theorem inp_712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_712 v hb
def cl_713 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,false),(28,false)]
theorem inp_713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_713 v hb
def cl_714 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,false),(28,false)]
theorem inp_714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_714 (by decide) v hb
def cl_715 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,false),(28,false)]
theorem inp_715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_715 v hb
def cl_716 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,false),(28,false)]
theorem inp_716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_716 v hb
def cl_717 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,false),(28,false)]
theorem inp_717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_717 (by decide) v hb
def cl_718 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,true),(21,false),(28,false)]
theorem inp_718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_718 (by decide) v hb
def cl_719 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,false),(28,false)]
theorem inp_719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_719 v hb
def cl_720 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,true),(21,false),(28,false)]
theorem inp_720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_720 (by decide) v hb
def cl_721 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,true),(28,false)]
theorem inp_721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_721 (by decide) v hb
def cl_722 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,true),(28,false)]
theorem inp_722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_722 (by decide) v hb
def cl_723 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,true),(28,false)]
theorem inp_723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_723 v hb
def cl_724 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,true),(28,false)]
theorem inp_724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_724 v hb
def cl_725 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,true),(28,false)]
theorem inp_725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_725 (by decide) v hb
def cl_726 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,true),(28,false)]
theorem inp_726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_726 (by decide) v hb
def cl_727 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,true),(28,false)]
theorem inp_727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_727 v hb
def cl_728 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,true),(28,false)]
theorem inp_728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_728 v hb
def cl_729 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,true),(28,false)]
theorem inp_729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_729 v hb
def cl_730 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,true),(28,false)]
theorem inp_730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_730 (by decide) v hb
def cl_731 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,true),(28,false)]
theorem inp_731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_731 v hb
def cl_732 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,true),(28,false)]
theorem inp_732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_732 v hb
def cl_733 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,true),(28,false)]
theorem inp_733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_733 (by decide) v hb
def cl_734 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,true),(21,true),(28,false)]
theorem inp_734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_734 (by decide) v hb
def cl_735 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,true),(28,false)]
theorem inp_735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_735 v hb
def cl_736 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,true),(28,false)]
theorem inp_736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_736 v hb
def cl_737 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,false),(28,true)]
theorem inp_737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_737 v hb
def cl_738 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,false),(28,true)]
theorem inp_738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_738 (by decide) v hb
def cl_739 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,false),(28,true)]
theorem inp_739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_739 v hb
def cl_740 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,false),(28,true)]
theorem inp_740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_740 v hb
def cl_741 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,false),(28,true)]
theorem inp_741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_741 (by decide) v hb
def cl_742 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,false),(28,true)]
theorem inp_742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_742 (by decide) v hb
def cl_743 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,false),(28,true)]
theorem inp_743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_743 v hb
end Percolation.NReplay
