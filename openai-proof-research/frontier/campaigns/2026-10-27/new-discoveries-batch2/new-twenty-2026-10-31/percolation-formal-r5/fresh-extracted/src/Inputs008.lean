import Inputs007
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_735 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,true),(28,false)]
theorem inp_735 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_735 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_735 (by decide) v h
def cl_736 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,true),(28,false)]
theorem inp_736 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_736 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_736 (by decide) v h
def cl_737 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,false),(28,true)]
theorem inp_737 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_737 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_737 (by decide) v h
def cl_739 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,false),(28,true)]
theorem inp_739 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_739 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_739 (by decide) v h
def cl_740 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,false),(28,true)]
theorem inp_740 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_740 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_740 (by decide) v h
def cl_743 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,false),(28,true)]
theorem inp_743 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_743 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_743 (by decide) v h
def cl_745 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,false),(28,true)]
theorem inp_745 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_745 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_745 (by decide) v h
def cl_747 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,false),(28,true)]
theorem inp_747 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_747 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_747 (by decide) v h
def cl_748 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,false),(28,true)]
theorem inp_748 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_748 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_748 (by decide) v h
def cl_751 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,false),(28,true)]
theorem inp_751 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_751 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_751 (by decide) v h
def cl_752 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,false),(28,true)]
theorem inp_752 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_752 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_752 (by decide) v h
def cl_755 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,true),(28,true)]
theorem inp_755 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_755 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_755 (by decide) v h
def cl_756 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,true),(28,true)]
theorem inp_756 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_756 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_756 (by decide) v h
def cl_759 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,true),(28,true)]
theorem inp_759 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_759 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_759 (by decide) v h
def cl_760 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,false),(21,true),(28,true)]
theorem inp_760 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_760 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_760 (by decide) v h
def cl_761 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,true),(28,true)]
theorem inp_761 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_761 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_761 (by decide) v h
def cl_763 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,true),(28,true)]
theorem inp_763 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_763 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_763 (by decide) v h
def cl_764 : CNF.NClause := [(73,false),(4,true),(7,true),(10,false),(18,true),(21,true),(28,true)]
theorem inp_764 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_764 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_764 (by decide) v h
def cl_766 : CNF.NClause := [(73,false),(4,true),(7,false),(10,true),(18,true),(21,true),(28,true)]
theorem inp_766 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_766 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_766 (by decide) v h
def cl_767 : CNF.NClause := [(73,false),(4,false),(7,true),(10,true),(18,true),(21,true),(28,true)]
theorem inp_767 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_767 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_767 (by decide) v h
def cl_768 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,true),(28,true)]
theorem inp_768 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_768 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_768 (by decide) v h
def cl_769 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,false),(29,false)]
theorem inp_769 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_769 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_769 (by decide) v h
def cl_770 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,false),(29,false)]
theorem inp_770 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_770 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_770 (by decide) v h
def cl_771 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,false),(29,false)]
theorem inp_771 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_771 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_771 (by decide) v h
def cl_772 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,false),(29,false)]
theorem inp_772 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_772 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_772 (by decide) v h
def cl_773 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,false),(29,false)]
theorem inp_773 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_773 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_773 (by decide) v h
def cl_774 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,false),(29,false)]
theorem inp_774 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_774 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_774 (by decide) v h
def cl_775 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,false),(29,false)]
theorem inp_775 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_775 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_775 (by decide) v h
def cl_776 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,false),(29,false)]
theorem inp_776 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_776 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_776 (by decide) v h
def cl_777 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,false),(29,false)]
theorem inp_777 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_777 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_777 (by decide) v h
def cl_779 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,false),(29,false)]
theorem inp_779 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_779 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_779 (by decide) v h
def cl_781 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,false),(29,false)]
theorem inp_781 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_781 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_781 (by decide) v h
def cl_782 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,false),(29,false)]
theorem inp_782 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_782 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_782 (by decide) v h
def cl_783 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,false),(29,false)]
theorem inp_783 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_783 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_783 (by decide) v h
def cl_784 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,true),(23,false),(29,false)]
theorem inp_784 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_784 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_784 (by decide) v h
def cl_787 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,true),(29,false)]
theorem inp_787 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_787 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_787 (by decide) v h
def cl_789 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,true),(29,false)]
theorem inp_789 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_789 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_789 (by decide) v h
def cl_790 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,true),(29,false)]
theorem inp_790 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_790 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_790 (by decide) v h
def cl_791 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,true),(29,false)]
theorem inp_791 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_791 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_791 (by decide) v h
def cl_792 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,true),(29,false)]
theorem inp_792 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_792 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_792 (by decide) v h
def cl_793 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,true),(29,false)]
theorem inp_793 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_793 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_793 (by decide) v h
def cl_795 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,true),(29,false)]
theorem inp_795 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_795 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_795 (by decide) v h
def cl_797 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,true),(29,false)]
theorem inp_797 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_797 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_797 (by decide) v h
def cl_798 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,true),(29,false)]
theorem inp_798 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_798 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_798 (by decide) v h
def cl_799 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,true),(29,false)]
theorem inp_799 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_799 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_799 (by decide) v h
def cl_800 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,true),(29,false)]
theorem inp_800 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_800 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_800 (by decide) v h
def cl_801 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,false),(29,true)]
theorem inp_801 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_801 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_801 (by decide) v h
def cl_803 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,false),(29,true)]
theorem inp_803 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_803 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_803 (by decide) v h
def cl_805 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,false),(29,true)]
theorem inp_805 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_805 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_805 (by decide) v h
def cl_806 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,false),(29,true)]
theorem inp_806 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_806 := by
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) cl_806 (by decide) v h
end Percolation.Replay
