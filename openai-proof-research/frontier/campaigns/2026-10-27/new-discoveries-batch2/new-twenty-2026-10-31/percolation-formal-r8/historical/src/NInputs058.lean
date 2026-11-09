import NInputs057
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3510 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,true),(58,true)]
theorem inp_3510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3510 v hb
def cl_3511 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,true),(58,true)]
theorem inp_3511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3511 v hb
def cl_3512 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,false),(52,true),(58,true)]
theorem inp_3512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3512 (by decide) v hb
def cl_3513 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,true),(58,true)]
theorem inp_3513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3513 (by decide) v hb
def cl_3514 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,true),(58,true)]
theorem inp_3514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3514 (by decide) v hb
def cl_3515 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,true),(58,true)]
theorem inp_3515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3515 (by decide) v hb
def cl_3516 : CNF.NClause := [(116,false),(34,true),(36,true),(43,false),(50,true),(52,true),(58,true)]
theorem inp_3516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3516 (by decide) v hb
def cl_3517 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,true),(58,true)]
theorem inp_3517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3517 (by decide) v hb
def cl_3518 : CNF.NClause := [(116,false),(34,true),(36,false),(43,true),(50,true),(52,true),(58,true)]
theorem inp_3518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3518 (by decide) v hb
def cl_3519 : CNF.NClause := [(116,false),(34,false),(36,true),(43,true),(50,true),(52,true),(58,true)]
theorem inp_3519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3519 v hb
def cl_3520 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,true),(58,true)]
theorem inp_3520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3520 v hb
def cl_3521 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,false),(60,false)]
theorem inp_3521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3521 (by decide) v hb
def cl_3522 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,false),(60,false)]
theorem inp_3522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3522 (by decide) v hb
def cl_3523 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,false),(60,false)]
theorem inp_3523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3523 v hb
def cl_3524 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,false),(60,false)]
theorem inp_3524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3524 v hb
def cl_3525 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,false),(60,false)]
theorem inp_3525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3525 (by decide) v hb
def cl_3526 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,false),(60,false)]
theorem inp_3526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3526 (by decide) v hb
def cl_3527 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,false),(60,false)]
theorem inp_3527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3527 (by decide) v hb
def cl_3528 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,false),(60,false)]
theorem inp_3528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3528 v hb
def cl_3529 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,false),(60,false)]
theorem inp_3529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3529 (by decide) v hb
def cl_3530 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,false),(60,false)]
theorem inp_3530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3530 (by decide) v hb
def cl_3531 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,false),(60,false)]
theorem inp_3531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3531 (by decide) v hb
def cl_3532 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,false),(60,false)]
theorem inp_3532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3532 v hb
def cl_3533 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,false),(60,false)]
theorem inp_3533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3533 (by decide) v hb
def cl_3534 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,true),(53,false),(60,false)]
theorem inp_3534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3534 (by decide) v hb
def cl_3535 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(53,false),(60,false)]
theorem inp_3535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3535 (by decide) v hb
def cl_3536 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,true),(53,false),(60,false)]
theorem inp_3536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3536 v hb
def cl_3537 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,true),(60,false)]
theorem inp_3537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3537 (by decide) v hb
def cl_3538 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,true),(60,false)]
theorem inp_3538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3538 (by decide) v hb
def cl_3539 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,true),(60,false)]
theorem inp_3539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3539 v hb
def cl_3540 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,true),(60,false)]
theorem inp_3540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3540 v hb
def cl_3541 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,true),(60,false)]
theorem inp_3541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3541 (by decide) v hb
def cl_3542 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,true),(60,false)]
theorem inp_3542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3542 (by decide) v hb
def cl_3543 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,true),(60,false)]
theorem inp_3543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3543 v hb
def cl_3544 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,true),(60,false)]
theorem inp_3544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3544 v hb
def cl_3545 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,true),(60,false)]
theorem inp_3545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3545 (by decide) v hb
def cl_3546 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,true),(60,false)]
theorem inp_3546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3546 (by decide) v hb
def cl_3547 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,true),(60,false)]
theorem inp_3547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3547 v hb
def cl_3548 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,true),(60,false)]
theorem inp_3548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3548 v hb
def cl_3549 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,true),(60,false)]
theorem inp_3549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3549 (by decide) v hb
def cl_3550 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,true),(53,true),(60,false)]
theorem inp_3550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3550 (by decide) v hb
def cl_3551 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(53,true),(60,false)]
theorem inp_3551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3551 (by decide) v hb
def cl_3552 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,true),(60,false)]
theorem inp_3552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3552 v hb
def cl_3553 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,false),(60,true)]
theorem inp_3553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3553 (by decide) v hb
def cl_3554 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,false),(60,true)]
theorem inp_3554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3554 (by decide) v hb
def cl_3555 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,false),(60,true)]
theorem inp_3555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3555 (by decide) v hb
def cl_3556 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,false),(60,true)]
theorem inp_3556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3556 v hb
def cl_3557 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,false),(60,true)]
theorem inp_3557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3557 (by decide) v hb
def cl_3558 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,false),(60,true)]
theorem inp_3558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3558 (by decide) v hb
def cl_3559 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,false),(60,true)]
theorem inp_3559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) cl_3559 (by decide) v hb
end Percolation.NReplay
