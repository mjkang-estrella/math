import NInputs062
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3785 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,false),(59,false)]
theorem inp_3785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3785 (by decide) v hb
def cl_3786 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,false),(59,false)]
theorem inp_3786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3786 (by decide) v hb
def cl_3787 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,false),(59,false)]
theorem inp_3787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3787 (by decide) v hb
def cl_3788 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,true),(53,false),(59,false)]
theorem inp_3788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3788 (by decide) v hb
def cl_3789 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,false),(59,false)]
theorem inp_3789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3789 (by decide) v hb
def cl_3790 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,true),(53,false),(59,false)]
theorem inp_3790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3790 (by decide) v hb
def cl_3791 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,true),(53,false),(59,false)]
theorem inp_3791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3791 (by decide) v hb
def cl_3792 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,true),(53,false),(59,false)]
theorem inp_3792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3792 (by decide) v hb
def cl_3793 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,true),(59,false)]
theorem inp_3793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3793 (by decide) v hb
def cl_3794 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,true),(59,false)]
theorem inp_3794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3794 (by decide) v hb
def cl_3795 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,true),(59,false)]
theorem inp_3795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3795 (by decide) v hb
def cl_3796 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,true),(59,false)]
theorem inp_3796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3796 v hb
def cl_3797 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,true),(59,false)]
theorem inp_3797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3797 v hb
def cl_3798 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,true),(59,false)]
theorem inp_3798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3798 (by decide) v hb
def cl_3799 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,true),(59,false)]
theorem inp_3799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3799 v hb
def cl_3800 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,false),(53,true),(59,false)]
theorem inp_3800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3800 (by decide) v hb
def cl_3801 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,true),(59,false)]
theorem inp_3801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3801 (by decide) v hb
def cl_3802 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,true),(59,false)]
theorem inp_3802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3802 v hb
def cl_3803 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,true),(59,false)]
theorem inp_3803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3803 v hb
def cl_3804 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,true),(53,true),(59,false)]
theorem inp_3804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3804 v hb
def cl_3805 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,true),(59,false)]
theorem inp_3805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3805 (by decide) v hb
def cl_3806 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,true),(53,true),(59,false)]
theorem inp_3806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3806 (by decide) v hb
def cl_3808 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,true),(53,true),(59,false)]
theorem inp_3808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3808 (by decide) v hb
def cl_3809 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,false),(59,true)]
theorem inp_3809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3809 (by decide) v hb
def cl_3810 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,false),(59,true)]
theorem inp_3810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3810 (by decide) v hb
def cl_3811 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,false),(59,true)]
theorem inp_3811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3811 (by decide) v hb
def cl_3812 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,false),(59,true)]
theorem inp_3812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3812 (by decide) v hb
def cl_3813 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,false),(59,true)]
theorem inp_3813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3813 (by decide) v hb
def cl_3814 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,false),(59,true)]
theorem inp_3814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3814 (by decide) v hb
def cl_3815 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,false),(59,true)]
theorem inp_3815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3815 (by decide) v hb
def cl_3816 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,false),(53,false),(59,true)]
theorem inp_3816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3816 (by decide) v hb
def cl_3817 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,false),(59,true)]
theorem inp_3817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3817 (by decide) v hb
def cl_3818 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,false),(59,true)]
theorem inp_3818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3818 (by decide) v hb
def cl_3819 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,false),(59,true)]
theorem inp_3819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3819 (by decide) v hb
def cl_3820 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,true),(53,false),(59,true)]
theorem inp_3820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3820 (by decide) v hb
def cl_3821 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,false),(59,true)]
theorem inp_3821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3821 (by decide) v hb
def cl_3822 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,true),(53,false),(59,true)]
theorem inp_3822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3822 (by decide) v hb
def cl_3823 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,true),(53,false),(59,true)]
theorem inp_3823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3823 (by decide) v hb
def cl_3824 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,true),(53,false),(59,true)]
theorem inp_3824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3824 (by decide) v hb
def cl_3825 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,true),(59,true)]
theorem inp_3825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3825 (by decide) v hb
def cl_3826 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,true),(59,true)]
theorem inp_3826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3826 (by decide) v hb
def cl_3827 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,true),(59,true)]
theorem inp_3827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3827 (by decide) v hb
def cl_3828 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,true),(59,true)]
theorem inp_3828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3828 v hb
def cl_3829 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,true),(59,true)]
theorem inp_3829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3829 v hb
def cl_3830 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,true),(59,true)]
theorem inp_3830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3830 (by decide) v hb
def cl_3831 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,true),(59,true)]
theorem inp_3831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3831 v hb
def cl_3832 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,false),(53,true),(59,true)]
theorem inp_3832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3832 (by decide) v hb
def cl_3833 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,true),(59,true)]
theorem inp_3833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3833 v hb
def cl_3834 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,true),(59,true)]
theorem inp_3834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3834 v hb
def cl_3835 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,true),(59,true)]
theorem inp_3835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) cl_3835 (by decide) v hb
end Percolation.NReplay
