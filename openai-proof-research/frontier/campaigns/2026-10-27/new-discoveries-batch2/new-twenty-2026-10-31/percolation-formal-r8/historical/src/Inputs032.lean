import Inputs031
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3572 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,true),(60,true)]
theorem inp_3572 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3572 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3572 (by decide) v h
def cl_3575 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,true),(60,true)]
theorem inp_3575 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3575 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3575 (by decide) v h
def cl_3579 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,true),(60,true)]
theorem inp_3579 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3579 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3579 (by decide) v h
def cl_3580 : CNF.NClause := [(117,false),(32,true),(36,true),(45,false),(49,true),(53,true),(60,true)]
theorem inp_3580 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3580 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3580 (by decide) v h
def cl_3584 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,true),(60,true)]
theorem inp_3584 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3584 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3584 (by decide) v h
def cl_3585 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,false),(35,false),(61,false)]
theorem inp_3585 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3585 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3585 (by decide) v h
def cl_3586 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,false),(61,false)]
theorem inp_3586 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3586 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3586 (by decide) v h
def cl_3587 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,false),(35,false),(61,false)]
theorem inp_3587 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3587 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3587 (by decide) v h
def cl_3588 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,false),(61,false)]
theorem inp_3588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3588 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3588 (by decide) v h
def cl_3589 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3589 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3589 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3589 (by decide) v h
def cl_3590 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3590 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3590 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3590 (by decide) v h
def cl_3591 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3591 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3591 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3591 (by decide) v h
def cl_3592 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,false),(61,false)]
theorem inp_3592 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3592 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3592 (by decide) v h
def cl_3593 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3593 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3593 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3593 (by decide) v h
def cl_3594 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3594 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3594 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3594 (by decide) v h
def cl_3595 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3595 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3595 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3595 (by decide) v h
def cl_3596 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,true),(35,false),(61,false)]
theorem inp_3596 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3596 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3596 (by decide) v h
def cl_3597 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3597 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3597 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3597 (by decide) v h
def cl_3598 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3598 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3598 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3598 (by decide) v h
def cl_3599 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3599 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3599 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3599 (by decide) v h
def cl_3600 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,true),(35,false),(61,false)]
theorem inp_3600 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3600 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3600 (by decide) v h
def cl_3601 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3601 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3601 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3601 (by decide) v h
def cl_3602 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3602 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3602 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3602 (by decide) v h
def cl_3603 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3603 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3603 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3603 (by decide) v h
def cl_3604 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,true),(61,false)]
theorem inp_3604 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3604 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3604 (by decide) v h
def cl_3605 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3605 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3605 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3605 (by decide) v h
def cl_3606 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3606 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3606 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3606 (by decide) v h
def cl_3607 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3607 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3607 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3607 (by decide) v h
def cl_3608 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,true),(61,false)]
theorem inp_3608 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3608 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3608 (by decide) v h
def cl_3609 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,true),(61,false)]
theorem inp_3609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3609 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3609 (by decide) v h
def cl_3610 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,true),(61,false)]
theorem inp_3610 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3610 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3610 (by decide) v h
def cl_3611 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,true),(61,false)]
theorem inp_3611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3611 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3611 (by decide) v h
def cl_3612 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,true),(35,true),(61,false)]
theorem inp_3612 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3612 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3612 (by decide) v h
def cl_3613 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,true),(61,false)]
theorem inp_3613 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3613 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3613 (by decide) v h
def cl_3614 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,true),(61,false)]
theorem inp_3614 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3614 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3614 (by decide) v h
def cl_3615 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(35,true),(61,false)]
theorem inp_3615 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3615 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3615 (by decide) v h
def cl_3625 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,false),(61,true)]
theorem inp_3625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3625 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3625 (by decide) v h
def cl_3626 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,false),(61,true)]
theorem inp_3626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3626 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3626 (by decide) v h
def cl_3627 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,false),(61,true)]
theorem inp_3627 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3627 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3627 (by decide) v h
def cl_3629 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,false),(61,true)]
theorem inp_3629 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3629 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3629 (by decide) v h
def cl_3630 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,false),(61,true)]
theorem inp_3630 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3630 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3630 (by decide) v h
def cl_3631 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(35,false),(61,true)]
theorem inp_3631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3631 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3631 (by decide) v h
def cl_3641 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,true),(61,true)]
theorem inp_3641 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3641 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3641 (by decide) v h
def cl_3642 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,true),(61,true)]
theorem inp_3642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3642 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3642 (by decide) v h
def cl_3645 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,true),(61,true)]
theorem inp_3645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3645 := by
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) cl_3645 (by decide) v h
def cl_3649 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,false),(60,false)]
theorem inp_3649 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3649 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3649 (by decide) v h
def cl_3650 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,false),(60,false)]
theorem inp_3650 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3650 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3650 (by decide) v h
def cl_3667 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,true),(60,false)]
theorem inp_3667 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3667 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3667 (by decide) v h
def cl_3671 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,false),(52,true),(60,false)]
theorem inp_3671 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3671 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3671 (by decide) v h
def cl_3675 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,true),(60,false)]
theorem inp_3675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3675 := by
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) cl_3675 (by decide) v h
end Percolation.Replay
