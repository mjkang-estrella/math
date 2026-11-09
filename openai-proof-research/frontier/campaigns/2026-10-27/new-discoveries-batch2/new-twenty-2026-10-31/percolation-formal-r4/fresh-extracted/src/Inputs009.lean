import Inputs008
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_807 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,false),(29,true)]
theorem inp_807 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_807 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_807 (by decide) v h
def cl_808 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,false),(29,true)]
theorem inp_808 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_808 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_808 (by decide) v h
def cl_809 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,false),(29,true)]
theorem inp_809 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_809 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_809 (by decide) v h
def cl_810 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,false),(29,true)]
theorem inp_810 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_810 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_810 (by decide) v h
def cl_811 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,false),(29,true)]
theorem inp_811 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_811 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_811 (by decide) v h
def cl_812 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,true),(23,false),(29,true)]
theorem inp_812 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_812 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_812 (by decide) v h
def cl_813 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,false),(29,true)]
theorem inp_813 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_813 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_813 (by decide) v h
def cl_814 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,false),(29,true)]
theorem inp_814 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_814 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_814 (by decide) v h
def cl_815 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,false),(29,true)]
theorem inp_815 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_815 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_815 (by decide) v h
def cl_816 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,false),(29,true)]
theorem inp_816 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_816 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_816 (by decide) v h
def cl_819 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,true),(29,true)]
theorem inp_819 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_819 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_819 (by decide) v h
def cl_821 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,true),(29,true)]
theorem inp_821 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_821 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_821 (by decide) v h
def cl_822 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,true),(29,true)]
theorem inp_822 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_822 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_822 (by decide) v h
def cl_823 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,true),(29,true)]
theorem inp_823 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_823 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_823 (by decide) v h
def cl_824 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,false),(23,true),(29,true)]
theorem inp_824 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_824 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_824 (by decide) v h
def cl_825 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,true),(29,true)]
theorem inp_825 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_825 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_825 (by decide) v h
def cl_827 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,true),(29,true)]
theorem inp_827 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_827 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_827 (by decide) v h
def cl_828 : CNF.NClause := [(74,false),(2,true),(6,true),(10,false),(19,true),(23,true),(29,true)]
theorem inp_828 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_828 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_828 (by decide) v h
def cl_829 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,true),(29,true)]
theorem inp_829 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_829 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_829 (by decide) v h
def cl_830 : CNF.NClause := [(74,false),(2,true),(6,false),(10,true),(19,true),(23,true),(29,true)]
theorem inp_830 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_830 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_830 (by decide) v h
def cl_831 : CNF.NClause := [(74,false),(2,false),(6,true),(10,true),(19,true),(23,true),(29,true)]
theorem inp_831 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_831 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_831 (by decide) v h
def cl_832 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,true),(29,true)]
theorem inp_832 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_832 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_832 (by decide) v h
def cl_833 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,false),(26,false)]
theorem inp_833 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_833 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_833 (by decide) v h
def cl_834 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,false),(26,false)]
theorem inp_834 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_834 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_834 (by decide) v h
def cl_835 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,false),(26,false)]
theorem inp_835 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_835 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_835 (by decide) v h
def cl_836 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,false),(26,false)]
theorem inp_836 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_836 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_836 (by decide) v h
def cl_837 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,false),(26,false)]
theorem inp_837 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_837 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_837 (by decide) v h
def cl_838 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,false),(26,false)]
theorem inp_838 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_838 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_838 (by decide) v h
def cl_839 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,false),(26,false)]
theorem inp_839 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_839 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_839 (by decide) v h
def cl_840 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,false),(26,false)]
theorem inp_840 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_840 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_840 (by decide) v h
def cl_843 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,false),(26,false)]
theorem inp_843 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_843 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_843 (by decide) v h
def cl_844 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,false),(26,false)]
theorem inp_844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_844 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_844 (by decide) v h
def cl_846 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,false),(26,false)]
theorem inp_846 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_846 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_846 (by decide) v h
def cl_847 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,false),(26,false)]
theorem inp_847 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_847 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_847 (by decide) v h
def cl_848 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,true),(22,false),(26,false)]
theorem inp_848 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_848 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_848 (by decide) v h
def cl_851 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,true),(26,false)]
theorem inp_851 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_851 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_851 (by decide) v h
def cl_853 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,true),(26,false)]
theorem inp_853 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_853 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_853 (by decide) v h
def cl_854 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,true),(26,false)]
theorem inp_854 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_854 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_854 (by decide) v h
def cl_855 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,true),(26,false)]
theorem inp_855 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_855 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_855 (by decide) v h
def cl_859 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,true),(26,false)]
theorem inp_859 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_859 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_859 (by decide) v h
def cl_862 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,true),(26,false)]
theorem inp_862 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_862 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_862 (by decide) v h
def cl_863 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,true),(26,false)]
theorem inp_863 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_863 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_863 (by decide) v h
def cl_865 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,false),(26,true)]
theorem inp_865 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_865 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_865 (by decide) v h
def cl_867 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,false),(26,true)]
theorem inp_867 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_867 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_867 (by decide) v h
def cl_868 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,false),(26,true)]
theorem inp_868 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_868 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_868 (by decide) v h
def cl_871 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,false),(26,true)]
theorem inp_871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_871 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_871 (by decide) v h
def cl_872 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,false),(26,true)]
theorem inp_872 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_872 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_872 (by decide) v h
def cl_875 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,false),(26,true)]
theorem inp_875 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_875 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_875 (by decide) v h
def cl_876 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,false),(26,true)]
theorem inp_876 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_876 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_876 (by decide) v h
def cl_879 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,false),(26,true)]
theorem inp_879 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_879 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_879 (by decide) v h
end Percolation.Replay
