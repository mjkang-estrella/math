import NInputs010
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_794 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,true),(29,false)]
theorem inp_794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_794 (by decide) v hb
def cl_795 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,true),(29,false)]
theorem inp_795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_795 v hb
def cl_796 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,true),(23,true),(29,false)]
theorem inp_796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_796 (by decide) v hb
def cl_797 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,true),(29,false)]
theorem inp_797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_797 v hb
def cl_798 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,true),(29,false)]
theorem inp_798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_798 v hb
def cl_799 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,true),(29,false)]
theorem inp_799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_799 v hb
def cl_800 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,true),(29,false)]
theorem inp_800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_800 v hb
def cl_801 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,false),(29,true)]
theorem inp_801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_801 v hb
def cl_802 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,false),(29,true)]
theorem inp_802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_802 (by decide) v hb
def cl_803 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,false),(29,true)]
theorem inp_803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_803 v hb
def cl_804 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,false),(29,true)]
theorem inp_804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_804 (by decide) v hb
def cl_805 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,false),(29,true)]
theorem inp_805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_805 v hb
def cl_806 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,false),(29,true)]
theorem inp_806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_806 v hb
def cl_807 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,false),(29,true)]
theorem inp_807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_807 v hb
def cl_808 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,false),(29,true)]
theorem inp_808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_808 v hb
def cl_809 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,false),(29,true)]
theorem inp_809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_809 v hb
def cl_810 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,false),(29,true)]
theorem inp_810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_810 v hb
def cl_811 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,false),(29,true)]
theorem inp_811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_811 v hb
def cl_812 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,true),(23,false),(29,true)]
theorem inp_812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_812 v hb
def cl_813 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,false),(29,true)]
theorem inp_813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_813 v hb
def cl_814 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,false),(29,true)]
theorem inp_814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_814 v hb
def cl_815 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,false),(29,true)]
theorem inp_815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_815 v hb
def cl_816 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,false),(29,true)]
theorem inp_816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_816 v hb
def cl_817 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,true),(29,true)]
theorem inp_817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_817 (by decide) v hb
def cl_818 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,true),(29,true)]
theorem inp_818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_818 (by decide) v hb
def cl_819 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,true),(29,true)]
theorem inp_819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_819 v hb
def cl_820 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,true),(29,true)]
theorem inp_820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_820 (by decide) v hb
def cl_821 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,true),(29,true)]
theorem inp_821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_821 v hb
def cl_822 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,true),(29,true)]
theorem inp_822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_822 v hb
def cl_823 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,true),(29,true)]
theorem inp_823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_823 v hb
def cl_824 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,false),(23,true),(29,true)]
theorem inp_824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_824 v hb
def cl_825 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,true),(29,true)]
theorem inp_825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_825 v hb
def cl_826 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,true),(29,true)]
theorem inp_826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_826 (by decide) v hb
def cl_827 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,true),(29,true)]
theorem inp_827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_827 v hb
def cl_828 : CNF.NClause := [(74,false),(2,true),(6,true),(10,false),(19,true),(23,true),(29,true)]
theorem inp_828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_828 v hb
def cl_829 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,true),(29,true)]
theorem inp_829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_829 v hb
def cl_830 : CNF.NClause := [(74,false),(2,true),(6,false),(10,true),(19,true),(23,true),(29,true)]
theorem inp_830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_830 v hb
def cl_831 : CNF.NClause := [(74,false),(2,false),(6,true),(10,true),(19,true),(23,true),(29,true)]
theorem inp_831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_831 v hb
def cl_832 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,true),(29,true)]
theorem inp_832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_832 v hb
def cl_833 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,false),(26,false)]
theorem inp_833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_833 v hb
def cl_834 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,false),(26,false)]
theorem inp_834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_834 v hb
def cl_835 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,false),(26,false)]
theorem inp_835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_835 v hb
def cl_836 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,false),(26,false)]
theorem inp_836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_836 v hb
def cl_837 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,false),(26,false)]
theorem inp_837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_837 v hb
def cl_838 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,false),(26,false)]
theorem inp_838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_838 v hb
def cl_839 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,false),(26,false)]
theorem inp_839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_839 v hb
def cl_840 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,false),(26,false)]
theorem inp_840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_840 v hb
def cl_841 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,false),(26,false)]
theorem inp_841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_841 (by decide) v hb
def cl_842 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,false),(26,false)]
theorem inp_842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_842 (by decide) v hb
def cl_843 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,false),(26,false)]
theorem inp_843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_843 v hb
end Percolation.NReplay
