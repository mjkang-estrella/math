import NInputs063
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3836 : CNF.NClause := [(121,false),(31,true),(39,true),(42,false),(50,true),(53,true),(59,true)]
theorem inp_3836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3836 (by decide) v hb
def cl_3837 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,true),(59,true)]
theorem inp_3837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3837 v hb
def cl_3838 : CNF.NClause := [(121,false),(31,true),(39,false),(42,true),(50,true),(53,true),(59,true)]
theorem inp_3838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3838 (by decide) v hb
def cl_3839 : CNF.NClause := [(121,false),(31,false),(39,true),(42,true),(50,true),(53,true),(59,true)]
theorem inp_3839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3839 (by decide) v hb
def cl_3840 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,true),(53,true),(59,true)]
theorem inp_3840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3840 (by decide) v hb
def cl_3841 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3841 v hb
def cl_3842 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3842 v hb
def cl_3843 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3843 v hb
def cl_3844 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,false),(57,false)]
theorem inp_3844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3844 v hb
def cl_3845 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(55,false),(57,false)]
theorem inp_3845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3845 (by decide) v hb
def cl_3846 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,false),(57,false)]
theorem inp_3846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3846 (by decide) v hb
def cl_3847 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,false),(57,false)]
theorem inp_3847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3847 v hb
def cl_3848 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,false),(55,false),(57,false)]
theorem inp_3848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3848 (by decide) v hb
def cl_3849 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,false),(57,false)]
theorem inp_3849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3849 (by decide) v hb
def cl_3850 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,false),(57,false)]
theorem inp_3850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3850 (by decide) v hb
def cl_3851 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,true),(55,false),(57,false)]
theorem inp_3851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3851 (by decide) v hb
def cl_3852 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,true),(55,false),(57,false)]
theorem inp_3852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3852 (by decide) v hb
def cl_3853 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,true),(55,false),(57,false)]
theorem inp_3853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3853 (by decide) v hb
def cl_3854 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,true),(55,false),(57,false)]
theorem inp_3854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3854 (by decide) v hb
def cl_3855 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,true),(55,false),(57,false)]
theorem inp_3855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3855 v hb
def cl_3856 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,true),(55,false),(57,false)]
theorem inp_3856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3856 v hb
def cl_3857 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,true),(57,false)]
theorem inp_3857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3857 (by decide) v hb
def cl_3858 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,true),(57,false)]
theorem inp_3858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3858 (by decide) v hb
def cl_3859 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,true),(57,false)]
theorem inp_3859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3859 (by decide) v hb
def cl_3860 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,true),(57,false)]
theorem inp_3860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3860 (by decide) v hb
def cl_3861 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(55,true),(57,false)]
theorem inp_3861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3861 (by decide) v hb
def cl_3862 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,true),(57,false)]
theorem inp_3862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3862 (by decide) v hb
def cl_3863 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,true),(57,false)]
theorem inp_3863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3863 v hb
def cl_3864 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,false),(55,true),(57,false)]
theorem inp_3864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3864 (by decide) v hb
def cl_3865 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,true),(57,false)]
theorem inp_3865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3865 (by decide) v hb
def cl_3866 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,true),(57,false)]
theorem inp_3866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3866 (by decide) v hb
def cl_3867 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,true),(55,true),(57,false)]
theorem inp_3867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3867 (by decide) v hb
def cl_3868 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,true),(55,true),(57,false)]
theorem inp_3868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3868 (by decide) v hb
def cl_3869 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,true),(55,true),(57,false)]
theorem inp_3869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3869 (by decide) v hb
def cl_3870 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,true),(55,true),(57,false)]
theorem inp_3870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3870 (by decide) v hb
def cl_3872 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,true),(57,false)]
theorem inp_3872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3872 v hb
def cl_3873 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,false),(57,true)]
theorem inp_3873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3873 (by decide) v hb
def cl_3874 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,false),(57,true)]
theorem inp_3874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3874 (by decide) v hb
def cl_3875 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,false),(57,true)]
theorem inp_3875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3875 v hb
def cl_3876 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,false),(57,true)]
theorem inp_3876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3876 v hb
def cl_3877 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(55,false),(57,true)]
theorem inp_3877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3877 (by decide) v hb
def cl_3878 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,false),(57,true)]
theorem inp_3878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3878 (by decide) v hb
def cl_3879 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,false),(57,true)]
theorem inp_3879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3879 v hb
def cl_3880 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,false),(55,false),(57,true)]
theorem inp_3880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3880 v hb
def cl_3881 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,false),(57,true)]
theorem inp_3881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3881 (by decide) v hb
def cl_3882 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,false),(57,true)]
theorem inp_3882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3882 (by decide) v hb
def cl_3884 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,true),(55,false),(57,true)]
theorem inp_3884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3884 (by decide) v hb
def cl_3885 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,true),(55,false),(57,true)]
theorem inp_3885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3885 (by decide) v hb
def cl_3886 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,true),(55,false),(57,true)]
theorem inp_3886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3886 (by decide) v hb
def cl_3888 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,false),(57,true)]
theorem inp_3888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3888 (by decide) v hb
end Percolation.NReplay
