import NInputs059
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3614 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,true),(61,false)]
theorem inp_3614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3614 v hb
def cl_3615 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(35,true),(61,false)]
theorem inp_3615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3615 v hb
def cl_3616 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,true),(35,true),(61,false)]
theorem inp_3616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3616 (by decide) v hb
def cl_3618 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,false),(61,true)]
theorem inp_3618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3618 (by decide) v hb
def cl_3620 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,false),(61,true)]
theorem inp_3620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3620 (by decide) v hb
def cl_3621 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,false),(61,true)]
theorem inp_3621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3621 (by decide) v hb
def cl_3622 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,false),(61,true)]
theorem inp_3622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3622 (by decide) v hb
def cl_3623 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,false),(61,true)]
theorem inp_3623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3623 (by decide) v hb
def cl_3624 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,false),(61,true)]
theorem inp_3624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3624 (by decide) v hb
def cl_3625 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,false),(61,true)]
theorem inp_3625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3625 v hb
def cl_3626 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,false),(61,true)]
theorem inp_3626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3626 v hb
def cl_3627 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,false),(61,true)]
theorem inp_3627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3627 v hb
def cl_3628 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,true),(35,false),(61,true)]
theorem inp_3628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3628 (by decide) v hb
def cl_3629 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,false),(61,true)]
theorem inp_3629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3629 v hb
def cl_3630 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,false),(61,true)]
theorem inp_3630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3630 v hb
def cl_3632 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,true),(35,false),(61,true)]
theorem inp_3632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3632 (by decide) v hb
def cl_3634 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,true),(61,true)]
theorem inp_3634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3634 (by decide) v hb
def cl_3636 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,true),(61,true)]
theorem inp_3636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3636 (by decide) v hb
def cl_3637 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,true),(61,true)]
theorem inp_3637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3637 (by decide) v hb
def cl_3638 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,true),(61,true)]
theorem inp_3638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3638 (by decide) v hb
def cl_3640 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,false),(35,true),(61,true)]
theorem inp_3640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3640 (by decide) v hb
def cl_3641 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,true),(61,true)]
theorem inp_3641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3641 v hb
def cl_3642 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,true),(61,true)]
theorem inp_3642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3642 v hb
def cl_3644 : CNF.NClause := [(118,false),(31,true),(32,true),(33,false),(34,true),(35,true),(61,true)]
theorem inp_3644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3644 (by decide) v hb
def cl_3645 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,true),(61,true)]
theorem inp_3645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3645 v hb
def cl_3646 : CNF.NClause := [(118,false),(31,true),(32,false),(33,true),(34,true),(35,true),(61,true)]
theorem inp_3646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3646 (by decide) v hb
def cl_3648 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,true),(35,true),(61,true)]
theorem inp_3648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3648 (by decide) v hb
def cl_3649 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,false),(60,false)]
theorem inp_3649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3649 v hb
def cl_3650 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,false),(60,false)]
theorem inp_3650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3650 v hb
def cl_3651 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,false),(60,false)]
theorem inp_3651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3651 (by decide) v hb
def cl_3652 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,false),(60,false)]
theorem inp_3652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3652 (by decide) v hb
def cl_3653 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,false),(60,false)]
theorem inp_3653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3653 (by decide) v hb
def cl_3654 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,false),(60,false)]
theorem inp_3654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3654 (by decide) v hb
def cl_3655 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,false),(52,false),(60,false)]
theorem inp_3655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3655 (by decide) v hb
def cl_3656 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,false),(52,false),(60,false)]
theorem inp_3656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3656 (by decide) v hb
def cl_3657 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,false),(60,false)]
theorem inp_3657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3657 (by decide) v hb
def cl_3658 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,false),(60,false)]
theorem inp_3658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3658 (by decide) v hb
def cl_3659 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,false),(60,false)]
theorem inp_3659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3659 (by decide) v hb
def cl_3660 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,true),(52,false),(60,false)]
theorem inp_3660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3660 (by decide) v hb
def cl_3661 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,true),(52,false),(60,false)]
theorem inp_3661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3661 (by decide) v hb
def cl_3662 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,true),(52,false),(60,false)]
theorem inp_3662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3662 (by decide) v hb
def cl_3663 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,false),(60,false)]
theorem inp_3663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3663 (by decide) v hb
def cl_3664 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,true),(52,false),(60,false)]
theorem inp_3664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3664 (by decide) v hb
def cl_3665 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,true),(60,false)]
theorem inp_3665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3665 (by decide) v hb
def cl_3666 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,true),(60,false)]
theorem inp_3666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3666 (by decide) v hb
def cl_3667 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,true),(60,false)]
theorem inp_3667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3667 v hb
def cl_3668 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,true),(60,false)]
theorem inp_3668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3668 (by decide) v hb
def cl_3669 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,true),(60,false)]
theorem inp_3669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3669 (by decide) v hb
def cl_3670 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,true),(60,false)]
theorem inp_3670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3670 (by decide) v hb
def cl_3672 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,false),(52,true),(60,false)]
theorem inp_3672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3672 (by decide) v hb
end Percolation.NReplay
