import NInputs060
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3673 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,true),(60,false)]
theorem inp_3673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3673 (by decide) v hb
def cl_3674 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,true),(60,false)]
theorem inp_3674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3674 (by decide) v hb
def cl_3675 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,true),(60,false)]
theorem inp_3675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3675 v hb
def cl_3676 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,true),(52,true),(60,false)]
theorem inp_3676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3676 (by decide) v hb
def cl_3677 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,true),(52,true),(60,false)]
theorem inp_3677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3677 (by decide) v hb
def cl_3678 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,true),(52,true),(60,false)]
theorem inp_3678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3678 (by decide) v hb
def cl_3679 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,true),(60,false)]
theorem inp_3679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3679 v hb
def cl_3680 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,true),(52,true),(60,false)]
theorem inp_3680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3680 (by decide) v hb
def cl_3681 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,false),(60,true)]
theorem inp_3681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3681 (by decide) v hb
def cl_3682 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,false),(60,true)]
theorem inp_3682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3682 (by decide) v hb
def cl_3683 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,false),(60,true)]
theorem inp_3683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3683 (by decide) v hb
def cl_3684 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,false),(60,true)]
theorem inp_3684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3684 (by decide) v hb
def cl_3685 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,false),(60,true)]
theorem inp_3685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3685 (by decide) v hb
def cl_3686 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,false),(60,true)]
theorem inp_3686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3686 (by decide) v hb
def cl_3687 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,false),(52,false),(60,true)]
theorem inp_3687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3687 (by decide) v hb
def cl_3688 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,false),(52,false),(60,true)]
theorem inp_3688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3688 (by decide) v hb
def cl_3689 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,false),(60,true)]
theorem inp_3689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3689 (by decide) v hb
def cl_3690 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,false),(60,true)]
theorem inp_3690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3690 (by decide) v hb
def cl_3691 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,false),(60,true)]
theorem inp_3691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3691 (by decide) v hb
def cl_3692 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,true),(52,false),(60,true)]
theorem inp_3692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3692 (by decide) v hb
def cl_3693 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,true),(52,false),(60,true)]
theorem inp_3693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3693 (by decide) v hb
def cl_3694 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,true),(52,false),(60,true)]
theorem inp_3694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3694 (by decide) v hb
def cl_3695 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,false),(60,true)]
theorem inp_3695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3695 (by decide) v hb
def cl_3696 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,true),(52,false),(60,true)]
theorem inp_3696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3696 (by decide) v hb
def cl_3697 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,true),(60,true)]
theorem inp_3697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3697 (by decide) v hb
def cl_3698 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,true),(60,true)]
theorem inp_3698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3698 (by decide) v hb
def cl_3699 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,true),(60,true)]
theorem inp_3699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3699 v hb
def cl_3700 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,true),(60,true)]
theorem inp_3700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3700 (by decide) v hb
def cl_3701 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,true),(60,true)]
theorem inp_3701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3701 (by decide) v hb
def cl_3702 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,true),(60,true)]
theorem inp_3702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3702 (by decide) v hb
def cl_3704 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,false),(52,true),(60,true)]
theorem inp_3704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3704 (by decide) v hb
def cl_3705 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,true),(60,true)]
theorem inp_3705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3705 (by decide) v hb
def cl_3706 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,true),(60,true)]
theorem inp_3706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3706 (by decide) v hb
def cl_3707 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,true),(60,true)]
theorem inp_3707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3707 v hb
def cl_3708 : CNF.NClause := [(119,false),(31,true),(40,true),(44,false),(48,true),(52,true),(60,true)]
theorem inp_3708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3708 (by decide) v hb
def cl_3710 : CNF.NClause := [(119,false),(31,true),(40,false),(44,true),(48,true),(52,true),(60,true)]
theorem inp_3710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3710 (by decide) v hb
def cl_3712 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,true),(52,true),(60,true)]
theorem inp_3712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3712 (by decide) v hb
def cl_3713 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,false),(58,false)]
theorem inp_3713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3713 (by decide) v hb
def cl_3714 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,false),(58,false)]
theorem inp_3714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3714 (by decide) v hb
def cl_3715 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,false),(58,false)]
theorem inp_3715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3715 v hb
def cl_3716 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,false),(58,false)]
theorem inp_3716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3716 v hb
def cl_3717 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(54,false),(58,false)]
theorem inp_3717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3717 (by decide) v hb
def cl_3718 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,false),(58,false)]
theorem inp_3718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3718 (by decide) v hb
def cl_3719 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,false),(54,false),(58,false)]
theorem inp_3719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3719 v hb
def cl_3720 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,false),(54,false),(58,false)]
theorem inp_3720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3720 (by decide) v hb
def cl_3721 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,false),(58,false)]
theorem inp_3721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3721 (by decide) v hb
def cl_3722 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,false),(58,false)]
theorem inp_3722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3722 (by decide) v hb
def cl_3723 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,false),(58,false)]
theorem inp_3723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3723 v hb
def cl_3724 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,true),(54,false),(58,false)]
theorem inp_3724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3724 (by decide) v hb
def cl_3725 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,true),(54,false),(58,false)]
theorem inp_3725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) cl_3725 (by decide) v hb
end Percolation.NReplay
