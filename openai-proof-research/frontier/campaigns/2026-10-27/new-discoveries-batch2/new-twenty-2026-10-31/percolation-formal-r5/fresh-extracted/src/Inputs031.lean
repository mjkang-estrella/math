import Inputs030
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3407 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,false),(59,false)]
theorem inp_3407 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3407 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3407 (by decide) v h
def cl_3417 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,true),(59,false)]
theorem inp_3417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3417 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3417 (by decide) v h
def cl_3419 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,true),(59,false)]
theorem inp_3419 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3419 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3419 (by decide) v h
def cl_3423 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,true),(59,false)]
theorem inp_3423 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3423 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3423 (by decide) v h
def cl_3424 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,true),(59,false)]
theorem inp_3424 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3424 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3424 (by decide) v h
def cl_3435 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,false),(59,true)]
theorem inp_3435 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3435 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3435 (by decide) v h
def cl_3436 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,true),(55,false),(59,true)]
theorem inp_3436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3436 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3436 (by decide) v h
def cl_3456 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,true),(59,true)]
theorem inp_3456 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3456 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3456 (by decide) v h
def cl_3457 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3457 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3457 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3457 (by decide) v h
def cl_3458 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3458 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3458 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3458 (by decide) v h
def cl_3459 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3459 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3459 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3459 (by decide) v h
def cl_3460 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3460 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3460 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3460 (by decide) v h
def cl_3463 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,false),(58,false)]
theorem inp_3463 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3463 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3463 (by decide) v h
def cl_3464 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,false),(52,false),(58,false)]
theorem inp_3464 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3464 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3464 (by decide) v h
def cl_3465 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,false),(58,false)]
theorem inp_3465 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3465 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3465 (by decide) v h
def cl_3466 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,false),(58,false)]
theorem inp_3466 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3466 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3466 (by decide) v h
def cl_3471 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,false),(58,false)]
theorem inp_3471 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3471 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3471 (by decide) v h
def cl_3473 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,true),(58,false)]
theorem inp_3473 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3473 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3473 (by decide) v h
def cl_3475 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,true),(58,false)]
theorem inp_3475 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3475 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3475 (by decide) v h
def cl_3477 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,true),(58,false)]
theorem inp_3477 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3477 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3477 (by decide) v h
def cl_3478 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,true),(58,false)]
theorem inp_3478 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3478 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3478 (by decide) v h
def cl_3479 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,true),(58,false)]
theorem inp_3479 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3479 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3479 (by decide) v h
def cl_3487 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,true),(58,false)]
theorem inp_3487 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3487 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3487 (by decide) v h
def cl_3488 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,true),(58,false)]
theorem inp_3488 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3488 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3488 (by decide) v h
def cl_3492 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,false),(58,true)]
theorem inp_3492 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3492 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3492 (by decide) v h
def cl_3493 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,false),(58,true)]
theorem inp_3493 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3493 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3493 (by decide) v h
def cl_3494 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,false),(58,true)]
theorem inp_3494 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3494 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3494 (by decide) v h
def cl_3495 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,false),(58,true)]
theorem inp_3495 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3495 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3495 (by decide) v h
def cl_3503 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,false),(58,true)]
theorem inp_3503 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3503 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3503 (by decide) v h
def cl_3509 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,true),(58,true)]
theorem inp_3509 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3509 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3509 (by decide) v h
def cl_3510 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,true),(58,true)]
theorem inp_3510 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3510 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3510 (by decide) v h
def cl_3511 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,true),(58,true)]
theorem inp_3511 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3511 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3511 (by decide) v h
def cl_3519 : CNF.NClause := [(116,false),(34,false),(36,true),(43,true),(50,true),(52,true),(58,true)]
theorem inp_3519 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3519 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3519 (by decide) v h
def cl_3520 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,true),(58,true)]
theorem inp_3520 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3520 := by
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3520 (by decide) v h
def cl_3523 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,false),(60,false)]
theorem inp_3523 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3523 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3523 (by decide) v h
def cl_3524 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,false),(60,false)]
theorem inp_3524 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3524 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3524 (by decide) v h
def cl_3528 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,false),(60,false)]
theorem inp_3528 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3528 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3528 (by decide) v h
def cl_3532 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,false),(60,false)]
theorem inp_3532 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3532 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3532 (by decide) v h
def cl_3536 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,true),(53,false),(60,false)]
theorem inp_3536 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3536 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3536 (by decide) v h
def cl_3539 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,true),(60,false)]
theorem inp_3539 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3539 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3539 (by decide) v h
def cl_3540 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,true),(60,false)]
theorem inp_3540 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3540 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3540 (by decide) v h
def cl_3543 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,true),(60,false)]
theorem inp_3543 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3543 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3543 (by decide) v h
def cl_3544 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,true),(60,false)]
theorem inp_3544 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3544 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3544 (by decide) v h
def cl_3547 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,true),(60,false)]
theorem inp_3547 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3547 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3547 (by decide) v h
def cl_3548 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,true),(60,false)]
theorem inp_3548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3548 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3548 (by decide) v h
def cl_3552 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,true),(60,false)]
theorem inp_3552 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3552 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3552 (by decide) v h
def cl_3556 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,false),(60,true)]
theorem inp_3556 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3556 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3556 (by decide) v h
def cl_3560 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,false),(60,true)]
theorem inp_3560 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3560 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3560 (by decide) v h
def cl_3564 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,false),(60,true)]
theorem inp_3564 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3564 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3564 (by decide) v h
def cl_3571 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,true),(60,true)]
theorem inp_3571 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3571 := by
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3571 (by decide) v h
end Percolation.Replay
