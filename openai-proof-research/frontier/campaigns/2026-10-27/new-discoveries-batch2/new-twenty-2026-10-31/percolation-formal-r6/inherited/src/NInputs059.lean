import NInputs058
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3560 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,false),(60,true)]
theorem inp_3560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3560 v hb
def cl_3561 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,false),(60,true)]
theorem inp_3561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3561 (by decide) v hb
def cl_3562 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,false),(60,true)]
theorem inp_3562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3562 (by decide) v hb
def cl_3563 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,false),(60,true)]
theorem inp_3563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3563 (by decide) v hb
def cl_3564 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,false),(60,true)]
theorem inp_3564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3564 v hb
def cl_3565 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,false),(60,true)]
theorem inp_3565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3565 (by decide) v hb
def cl_3566 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,true),(53,false),(60,true)]
theorem inp_3566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3566 (by decide) v hb
def cl_3567 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(53,false),(60,true)]
theorem inp_3567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3567 (by decide) v hb
def cl_3568 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,false),(60,true)]
theorem inp_3568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3568 (by decide) v hb
def cl_3569 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,true),(60,true)]
theorem inp_3569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3569 (by decide) v hb
def cl_3570 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,true),(60,true)]
theorem inp_3570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3570 (by decide) v hb
def cl_3571 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,true),(60,true)]
theorem inp_3571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3571 v hb
def cl_3572 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,true),(60,true)]
theorem inp_3572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3572 v hb
def cl_3573 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,true),(60,true)]
theorem inp_3573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3573 (by decide) v hb
def cl_3574 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,true),(60,true)]
theorem inp_3574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3574 (by decide) v hb
def cl_3575 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,true),(60,true)]
theorem inp_3575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3575 v hb
def cl_3576 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,false),(53,true),(60,true)]
theorem inp_3576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3576 (by decide) v hb
def cl_3577 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,true),(60,true)]
theorem inp_3577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3577 (by decide) v hb
def cl_3578 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,true),(60,true)]
theorem inp_3578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3578 (by decide) v hb
def cl_3579 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,true),(60,true)]
theorem inp_3579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3579 v hb
def cl_3580 : CNF.NClause := [(117,false),(32,true),(36,true),(45,false),(49,true),(53,true),(60,true)]
theorem inp_3580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3580 v hb
def cl_3581 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,true),(60,true)]
theorem inp_3581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3581 (by decide) v hb
def cl_3583 : CNF.NClause := [(117,false),(32,false),(36,true),(45,true),(49,true),(53,true),(60,true)]
theorem inp_3583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3583 (by decide) v hb
def cl_3584 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,true),(60,true)]
theorem inp_3584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3584 v hb
def cl_3585 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,false),(35,false),(61,false)]
theorem inp_3585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3585 v hb
def cl_3587 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,false),(35,false),(61,false)]
theorem inp_3587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3587 v hb
def cl_3588 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,false),(61,false)]
theorem inp_3588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3588 v hb
def cl_3589 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3589 v hb
def cl_3590 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3590 v hb
def cl_3591 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3591 v hb
def cl_3592 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3592 v hb
def cl_3593 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3593 v hb
def cl_3594 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3594 v hb
def cl_3595 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3595 v hb
def cl_3596 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3596 v hb
def cl_3597 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3597 v hb
def cl_3598 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3598 v hb
def cl_3599 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3599 v hb
def cl_3600 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3600 v hb
def cl_3601 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3601 v hb
def cl_3602 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3602 v hb
def cl_3603 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3603 v hb
def cl_3604 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3604 v hb
def cl_3605 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3605 v hb
def cl_3606 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3606 v hb
def cl_3607 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3607 v hb
def cl_3608 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3608 v hb
def cl_3609 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,true),(61,false)]
theorem inp_3609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3609 v hb
def cl_3610 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,true),(61,false)]
theorem inp_3610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3610 v hb
def cl_3613 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,true),(61,false)]
theorem inp_3613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3613 v hb
end Percolation.NReplay
