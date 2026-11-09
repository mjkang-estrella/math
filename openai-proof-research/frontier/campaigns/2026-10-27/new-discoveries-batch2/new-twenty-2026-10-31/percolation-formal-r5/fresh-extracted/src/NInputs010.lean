import NInputs009
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_744 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,false),(28,true)]
theorem inp_744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_744 (by decide) v hb
def cl_745 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,false),(28,true)]
theorem inp_745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_745 v hb
def cl_746 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,false),(28,true)]
theorem inp_746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_746 (by decide) v hb
def cl_747 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,false),(28,true)]
theorem inp_747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_747 v hb
def cl_748 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,false),(28,true)]
theorem inp_748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_748 v hb
def cl_749 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,false),(28,true)]
theorem inp_749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_749 (by decide) v hb
def cl_750 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,true),(21,false),(28,true)]
theorem inp_750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_750 (by decide) v hb
def cl_751 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,false),(28,true)]
theorem inp_751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_751 v hb
def cl_752 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,false),(28,true)]
theorem inp_752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_752 v hb
def cl_753 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,true),(28,true)]
theorem inp_753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_753 (by decide) v hb
def cl_754 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,true),(28,true)]
theorem inp_754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_754 (by decide) v hb
def cl_755 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,true),(28,true)]
theorem inp_755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_755 v hb
def cl_756 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,true),(28,true)]
theorem inp_756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_756 v hb
def cl_757 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,true),(28,true)]
theorem inp_757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_757 (by decide) v hb
def cl_758 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,true),(28,true)]
theorem inp_758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_758 (by decide) v hb
def cl_759 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,true),(28,true)]
theorem inp_759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_759 v hb
def cl_760 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,false),(21,true),(28,true)]
theorem inp_760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_760 v hb
def cl_761 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,true),(28,true)]
theorem inp_761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_761 v hb
def cl_762 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,true),(28,true)]
theorem inp_762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_762 (by decide) v hb
def cl_763 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,true),(28,true)]
theorem inp_763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_763 v hb
def cl_764 : CNF.NClause := [(73,false),(4,true),(7,true),(10,false),(18,true),(21,true),(28,true)]
theorem inp_764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_764 v hb
def cl_765 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,true),(28,true)]
theorem inp_765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_765 (by decide) v hb
def cl_766 : CNF.NClause := [(73,false),(4,true),(7,false),(10,true),(18,true),(21,true),(28,true)]
theorem inp_766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_766 v hb
def cl_767 : CNF.NClause := [(73,false),(4,false),(7,true),(10,true),(18,true),(21,true),(28,true)]
theorem inp_767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_767 v hb
def cl_768 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,true),(28,true)]
theorem inp_768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_768 v hb
def cl_769 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,false),(29,false)]
theorem inp_769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_769 v hb
def cl_770 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,false),(29,false)]
theorem inp_770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_770 v hb
def cl_771 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,false),(29,false)]
theorem inp_771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_771 v hb
def cl_772 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,false),(29,false)]
theorem inp_772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_772 v hb
def cl_773 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,false),(29,false)]
theorem inp_773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_773 v hb
def cl_774 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,false),(29,false)]
theorem inp_774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_774 v hb
def cl_775 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,false),(29,false)]
theorem inp_775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_775 v hb
def cl_776 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,false),(29,false)]
theorem inp_776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_776 v hb
def cl_777 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,false),(29,false)]
theorem inp_777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_777 v hb
def cl_778 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,false),(29,false)]
theorem inp_778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_778 (by decide) v hb
def cl_779 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,false),(29,false)]
theorem inp_779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_779 v hb
def cl_780 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,true),(23,false),(29,false)]
theorem inp_780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_780 (by decide) v hb
def cl_781 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,false),(29,false)]
theorem inp_781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_781 v hb
def cl_782 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,false),(29,false)]
theorem inp_782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_782 v hb
def cl_783 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,false),(29,false)]
theorem inp_783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_783 v hb
def cl_784 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,true),(23,false),(29,false)]
theorem inp_784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_784 v hb
def cl_785 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,true),(29,false)]
theorem inp_785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_785 (by decide) v hb
def cl_786 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,true),(29,false)]
theorem inp_786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_786 (by decide) v hb
def cl_787 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,true),(29,false)]
theorem inp_787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_787 v hb
def cl_788 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,true),(29,false)]
theorem inp_788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_788 (by decide) v hb
def cl_789 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,true),(29,false)]
theorem inp_789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_789 v hb
def cl_790 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,true),(29,false)]
theorem inp_790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_790 v hb
def cl_791 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,true),(29,false)]
theorem inp_791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_791 v hb
def cl_792 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,true),(29,false)]
theorem inp_792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_792 v hb
def cl_793 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,true),(29,false)]
theorem inp_793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_793 v hb
end Percolation.NReplay
