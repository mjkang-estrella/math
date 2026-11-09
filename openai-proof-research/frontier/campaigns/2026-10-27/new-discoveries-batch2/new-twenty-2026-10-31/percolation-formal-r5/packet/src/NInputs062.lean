import NInputs061
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3726 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,true),(54,false),(58,false)]
theorem inp_3726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3726 (by decide) v hb
def cl_3727 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,true),(54,false),(58,false)]
theorem inp_3727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3727 v hb
def cl_3728 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,true),(54,false),(58,false)]
theorem inp_3728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3728 (by decide) v hb
def cl_3729 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,true),(58,false)]
theorem inp_3729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3729 (by decide) v hb
def cl_3730 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,true),(58,false)]
theorem inp_3730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3730 (by decide) v hb
def cl_3731 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,true),(58,false)]
theorem inp_3731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3731 v hb
def cl_3732 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,true),(58,false)]
theorem inp_3732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3732 (by decide) v hb
def cl_3733 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(54,true),(58,false)]
theorem inp_3733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3733 (by decide) v hb
def cl_3734 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,true),(58,false)]
theorem inp_3734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3734 (by decide) v hb
def cl_3736 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,false),(54,true),(58,false)]
theorem inp_3736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3736 (by decide) v hb
def cl_3737 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,true),(58,false)]
theorem inp_3737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3737 (by decide) v hb
def cl_3738 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,true),(58,false)]
theorem inp_3738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3738 (by decide) v hb
def cl_3739 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,true),(58,false)]
theorem inp_3739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3739 v hb
def cl_3740 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,true),(54,true),(58,false)]
theorem inp_3740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3740 (by decide) v hb
def cl_3741 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,true),(54,true),(58,false)]
theorem inp_3741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3741 (by decide) v hb
def cl_3742 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,true),(54,true),(58,false)]
theorem inp_3742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3742 (by decide) v hb
def cl_3744 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,true),(54,true),(58,false)]
theorem inp_3744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3744 (by decide) v hb
def cl_3745 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,false),(58,true)]
theorem inp_3745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3745 (by decide) v hb
def cl_3746 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,false),(58,true)]
theorem inp_3746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3746 (by decide) v hb
def cl_3747 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,false),(58,true)]
theorem inp_3747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3747 v hb
def cl_3748 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,false),(58,true)]
theorem inp_3748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3748 v hb
def cl_3750 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,false),(58,true)]
theorem inp_3750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3750 (by decide) v hb
def cl_3752 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,false),(54,false),(58,true)]
theorem inp_3752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3752 v hb
def cl_3753 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,false),(58,true)]
theorem inp_3753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3753 (by decide) v hb
def cl_3754 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,false),(58,true)]
theorem inp_3754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3754 (by decide) v hb
def cl_3755 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,false),(58,true)]
theorem inp_3755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3755 v hb
def cl_3756 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,true),(54,false),(58,true)]
theorem inp_3756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3756 (by decide) v hb
def cl_3757 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,true),(54,false),(58,true)]
theorem inp_3757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3757 (by decide) v hb
def cl_3758 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,true),(54,false),(58,true)]
theorem inp_3758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3758 (by decide) v hb
def cl_3760 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,true),(54,false),(58,true)]
theorem inp_3760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3760 (by decide) v hb
def cl_3761 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,true),(58,true)]
theorem inp_3761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3761 (by decide) v hb
def cl_3762 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,true),(58,true)]
theorem inp_3762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3762 (by decide) v hb
def cl_3763 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,true),(58,true)]
theorem inp_3763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3763 v hb
def cl_3764 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,true),(58,true)]
theorem inp_3764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3764 (by decide) v hb
def cl_3765 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(54,true),(58,true)]
theorem inp_3765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3765 (by decide) v hb
def cl_3766 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,true),(58,true)]
theorem inp_3766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3766 (by decide) v hb
def cl_3768 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,false),(54,true),(58,true)]
theorem inp_3768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3768 (by decide) v hb
def cl_3769 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,true),(58,true)]
theorem inp_3769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3769 (by decide) v hb
def cl_3770 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,true),(58,true)]
theorem inp_3770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3770 (by decide) v hb
def cl_3772 : CNF.NClause := [(120,false),(31,true),(38,true),(45,false),(47,true),(54,true),(58,true)]
theorem inp_3772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3772 (by decide) v hb
def cl_3774 : CNF.NClause := [(120,false),(31,true),(38,false),(45,true),(47,true),(54,true),(58,true)]
theorem inp_3774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3774 (by decide) v hb
def cl_3776 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,true),(54,true),(58,true)]
theorem inp_3776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3776 (by decide) v hb
def cl_3777 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,false),(59,false)]
theorem inp_3777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3777 v hb
def cl_3778 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,false),(59,false)]
theorem inp_3778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3778 v hb
def cl_3779 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,false),(59,false)]
theorem inp_3779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3779 (by decide) v hb
def cl_3780 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,false),(59,false)]
theorem inp_3780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3780 (by decide) v hb
def cl_3781 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,false),(59,false)]
theorem inp_3781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3781 v hb
def cl_3782 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,false),(59,false)]
theorem inp_3782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3782 (by decide) v hb
def cl_3783 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,false),(59,false)]
theorem inp_3783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3783 (by decide) v hb
def cl_3784 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,false),(53,false),(59,false)]
theorem inp_3784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3784 (by decide) v hb
end Percolation.NReplay
