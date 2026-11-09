import NInputs056
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3460 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3460 v hb
def cl_3461 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,false),(58,false)]
theorem inp_3461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3461 (by decide) v hb
def cl_3462 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,false),(58,false)]
theorem inp_3462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3462 (by decide) v hb
def cl_3463 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,false),(58,false)]
theorem inp_3463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3463 v hb
def cl_3464 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,false),(52,false),(58,false)]
theorem inp_3464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3464 v hb
def cl_3465 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,false),(58,false)]
theorem inp_3465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3465 v hb
def cl_3466 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,false),(58,false)]
theorem inp_3466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3466 v hb
def cl_3467 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,false),(58,false)]
theorem inp_3467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3467 (by decide) v hb
def cl_3468 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,true),(52,false),(58,false)]
theorem inp_3468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3468 (by decide) v hb
def cl_3469 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,false),(58,false)]
theorem inp_3469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3469 (by decide) v hb
def cl_3470 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,true),(52,false),(58,false)]
theorem inp_3470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3470 (by decide) v hb
def cl_3471 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,false),(58,false)]
theorem inp_3471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3471 v hb
def cl_3472 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,true),(52,false),(58,false)]
theorem inp_3472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3472 (by decide) v hb
def cl_3473 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,true),(58,false)]
theorem inp_3473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3473 v hb
def cl_3474 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,true),(58,false)]
theorem inp_3474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3474 (by decide) v hb
def cl_3475 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,true),(58,false)]
theorem inp_3475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3475 v hb
def cl_3476 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,true),(58,false)]
theorem inp_3476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3476 (by decide) v hb
def cl_3477 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,true),(58,false)]
theorem inp_3477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3477 v hb
def cl_3478 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,true),(58,false)]
theorem inp_3478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3478 v hb
def cl_3479 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,true),(58,false)]
theorem inp_3479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3479 v hb
def cl_3480 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,false),(52,true),(58,false)]
theorem inp_3480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3480 (by decide) v hb
def cl_3481 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,true),(58,false)]
theorem inp_3481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3481 (by decide) v hb
def cl_3482 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,true),(58,false)]
theorem inp_3482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3482 (by decide) v hb
def cl_3483 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,true),(58,false)]
theorem inp_3483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3483 (by decide) v hb
def cl_3484 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,true),(52,true),(58,false)]
theorem inp_3484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3484 (by decide) v hb
def cl_3485 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,true),(58,false)]
theorem inp_3485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3485 (by decide) v hb
def cl_3486 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,true),(52,true),(58,false)]
theorem inp_3486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3486 (by decide) v hb
def cl_3487 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,true),(58,false)]
theorem inp_3487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3487 v hb
def cl_3488 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,true),(58,false)]
theorem inp_3488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3488 v hb
def cl_3489 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,false),(58,true)]
theorem inp_3489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3489 (by decide) v hb
def cl_3490 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,false),(58,true)]
theorem inp_3490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3490 (by decide) v hb
def cl_3491 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,false),(58,true)]
theorem inp_3491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3491 (by decide) v hb
def cl_3492 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,false),(58,true)]
theorem inp_3492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3492 v hb
def cl_3493 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,false),(58,true)]
theorem inp_3493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3493 v hb
def cl_3494 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,false),(58,true)]
theorem inp_3494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3494 v hb
def cl_3495 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,false),(58,true)]
theorem inp_3495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3495 v hb
def cl_3496 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,false),(52,false),(58,true)]
theorem inp_3496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3496 (by decide) v hb
def cl_3497 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,false),(58,true)]
theorem inp_3497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3497 (by decide) v hb
def cl_3498 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,false),(58,true)]
theorem inp_3498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3498 (by decide) v hb
def cl_3499 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,false),(58,true)]
theorem inp_3499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3499 (by decide) v hb
def cl_3500 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,true),(52,false),(58,true)]
theorem inp_3500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3500 (by decide) v hb
def cl_3501 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,false),(58,true)]
theorem inp_3501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3501 (by decide) v hb
def cl_3502 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,true),(52,false),(58,true)]
theorem inp_3502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3502 (by decide) v hb
def cl_3503 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,false),(58,true)]
theorem inp_3503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3503 v hb
def cl_3504 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,false),(58,true)]
theorem inp_3504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3504 (by decide) v hb
def cl_3505 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,true),(58,true)]
theorem inp_3505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3505 (by decide) v hb
def cl_3506 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,true),(58,true)]
theorem inp_3506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3506 (by decide) v hb
def cl_3507 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,true),(58,true)]
theorem inp_3507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3507 (by decide) v hb
def cl_3508 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,true),(58,true)]
theorem inp_3508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) cl_3508 (by decide) v hb
def cl_3509 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,true),(58,true)]
theorem inp_3509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3509 v hb
end Percolation.NReplay
