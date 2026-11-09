import Inputs032
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3679 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,true),(60,false)]
theorem inp_3679 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3679 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3679 (by decide) v h
def cl_3699 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,true),(60,true)]
theorem inp_3699 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3699 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3699 (by decide) v h
def cl_3703 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,false),(52,true),(60,true)]
theorem inp_3703 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3703 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3703 (by decide) v h
def cl_3707 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,true),(60,true)]
theorem inp_3707 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3707 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3707 (by decide) v h
def cl_3715 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,false),(58,false)]
theorem inp_3715 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3715 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3715 (by decide) v h
def cl_3716 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,false),(58,false)]
theorem inp_3716 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3716 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3716 (by decide) v h
def cl_3719 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,false),(54,false),(58,false)]
theorem inp_3719 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3719 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3719 (by decide) v h
def cl_3723 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,false),(58,false)]
theorem inp_3723 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3723 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3723 (by decide) v h
def cl_3727 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,true),(54,false),(58,false)]
theorem inp_3727 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3727 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3727 (by decide) v h
def cl_3731 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,true),(58,false)]
theorem inp_3731 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3731 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3731 (by decide) v h
def cl_3735 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,false),(54,true),(58,false)]
theorem inp_3735 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3735 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3735 (by decide) v h
def cl_3739 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,true),(58,false)]
theorem inp_3739 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3739 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3739 (by decide) v h
def cl_3743 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,true),(54,true),(58,false)]
theorem inp_3743 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3743 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3743 (by decide) v h
def cl_3747 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,false),(58,true)]
theorem inp_3747 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3747 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3747 (by decide) v h
def cl_3748 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,false),(58,true)]
theorem inp_3748 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3748 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3748 (by decide) v h
def cl_3751 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,false),(54,false),(58,true)]
theorem inp_3751 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3751 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3751 (by decide) v h
def cl_3752 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,false),(54,false),(58,true)]
theorem inp_3752 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3752 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3752 (by decide) v h
def cl_3755 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,false),(58,true)]
theorem inp_3755 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3755 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3755 (by decide) v h
def cl_3759 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,true),(54,false),(58,true)]
theorem inp_3759 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3759 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3759 (by decide) v h
def cl_3763 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,true),(58,true)]
theorem inp_3763 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3763 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3763 (by decide) v h
def cl_3767 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,false),(54,true),(58,true)]
theorem inp_3767 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3767 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3767 (by decide) v h
def cl_3771 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,true),(58,true)]
theorem inp_3771 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3771 := by
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3771 (by decide) v h
def cl_3777 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,false),(59,false)]
theorem inp_3777 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3777 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3777 (by decide) v h
def cl_3778 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,false),(59,false)]
theorem inp_3778 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3778 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3778 (by decide) v h
def cl_3781 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,false),(59,false)]
theorem inp_3781 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3781 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3781 (by decide) v h
def cl_3796 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,true),(59,false)]
theorem inp_3796 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3796 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3796 (by decide) v h
def cl_3797 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,true),(59,false)]
theorem inp_3797 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3797 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3797 (by decide) v h
def cl_3799 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,true),(59,false)]
theorem inp_3799 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3799 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3799 (by decide) v h
def cl_3802 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,true),(59,false)]
theorem inp_3802 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3802 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3802 (by decide) v h
def cl_3803 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,true),(59,false)]
theorem inp_3803 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3803 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3803 (by decide) v h
def cl_3804 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,true),(53,true),(59,false)]
theorem inp_3804 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3804 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3804 (by decide) v h
def cl_3828 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,true),(59,true)]
theorem inp_3828 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3828 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3828 (by decide) v h
def cl_3829 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,true),(59,true)]
theorem inp_3829 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3829 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3829 (by decide) v h
def cl_3831 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,true),(59,true)]
theorem inp_3831 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3831 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3831 (by decide) v h
def cl_3833 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,true),(59,true)]
theorem inp_3833 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3833 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3833 (by decide) v h
def cl_3834 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,true),(59,true)]
theorem inp_3834 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3834 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3834 (by decide) v h
def cl_3837 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,true),(59,true)]
theorem inp_3837 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3837 := by
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3837 (by decide) v h
def cl_3841 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3841 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3841 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3841 (by decide) v h
def cl_3842 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3842 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3842 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3842 (by decide) v h
def cl_3843 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3843 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3843 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3843 (by decide) v h
def cl_3844 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3844 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3844 (by decide) v h
def cl_3847 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,false),(57,false)]
theorem inp_3847 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3847 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3847 (by decide) v h
def cl_3855 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,true),(55,false),(57,false)]
theorem inp_3855 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3855 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3855 (by decide) v h
def cl_3856 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,true),(55,false),(57,false)]
theorem inp_3856 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3856 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3856 (by decide) v h
def cl_3863 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,true),(57,false)]
theorem inp_3863 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3863 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3863 (by decide) v h
def cl_3871 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,true),(55,true),(57,false)]
theorem inp_3871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3871 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3871 (by decide) v h
def cl_3872 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,true),(57,false)]
theorem inp_3872 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3872 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3872 (by decide) v h
def cl_3875 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,false),(57,true)]
theorem inp_3875 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3875 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3875 (by decide) v h
def cl_3876 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,false),(57,true)]
theorem inp_3876 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3876 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3876 (by decide) v h
def cl_3879 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,false),(57,true)]
theorem inp_3879 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3879 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3879 (by decide) v h
end Percolation.Replay
