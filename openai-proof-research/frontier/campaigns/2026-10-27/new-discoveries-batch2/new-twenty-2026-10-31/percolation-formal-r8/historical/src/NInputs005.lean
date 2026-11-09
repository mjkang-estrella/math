import NInputs004
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_461 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,false),(27,false)]
theorem inp_461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_461 (by decide) v hb
def cl_462 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,true),(20,false),(27,false)]
theorem inp_462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_462 (by decide) v hb
def cl_463 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,true),(20,false),(27,false)]
theorem inp_463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_463 (by decide) v hb
def cl_464 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,true),(20,false),(27,false)]
theorem inp_464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_464 (by decide) v hb
def cl_465 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,true),(27,false)]
theorem inp_465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_465 (by decide) v hb
def cl_466 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,true),(27,false)]
theorem inp_466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_466 (by decide) v hb
def cl_467 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,true),(27,false)]
theorem inp_467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_467 v hb
def cl_468 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,true),(27,false)]
theorem inp_468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_468 (by decide) v hb
def cl_469 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,true),(27,false)]
theorem inp_469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_469 (by decide) v hb
def cl_470 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,true),(27,false)]
theorem inp_470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_470 (by decide) v hb
def cl_471 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,true),(27,false)]
theorem inp_471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_471 (by decide) v hb
def cl_472 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,true),(27,false)]
theorem inp_472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_472 (by decide) v hb
def cl_473 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,true),(27,false)]
theorem inp_473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_473 v hb
def cl_474 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,true),(27,false)]
theorem inp_474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_474 v hb
def cl_475 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,true),(27,false)]
theorem inp_475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_475 v hb
def cl_476 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,true),(20,true),(27,false)]
theorem inp_476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_476 (by decide) v hb
def cl_477 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,true),(27,false)]
theorem inp_477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_477 (by decide) v hb
def cl_478 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,true),(20,true),(27,false)]
theorem inp_478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_478 (by decide) v hb
def cl_479 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,true),(20,true),(27,false)]
theorem inp_479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_479 (by decide) v hb
def cl_480 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,true),(27,false)]
theorem inp_480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_480 v hb
def cl_481 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,false),(27,true)]
theorem inp_481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_481 v hb
def cl_482 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,false),(27,true)]
theorem inp_482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_482 v hb
def cl_483 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,false),(27,true)]
theorem inp_483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_483 v hb
def cl_484 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,false),(27,true)]
theorem inp_484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_484 v hb
def cl_485 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,false),(27,true)]
theorem inp_485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_485 (by decide) v hb
def cl_486 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,false),(27,true)]
theorem inp_486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_486 v hb
def cl_487 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,false),(27,true)]
theorem inp_487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_487 v hb
def cl_488 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,false),(27,true)]
theorem inp_488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_488 v hb
def cl_489 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,false),(27,true)]
theorem inp_489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_489 v hb
def cl_490 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,false),(27,true)]
theorem inp_490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_490 v hb
def cl_491 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,false),(27,true)]
theorem inp_491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_491 v hb
def cl_492 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,true),(20,false),(27,true)]
theorem inp_492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_492 v hb
def cl_493 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,false),(27,true)]
theorem inp_493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_493 (by decide) v hb
def cl_494 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,true),(20,false),(27,true)]
theorem inp_494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_494 (by decide) v hb
def cl_495 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,true),(20,false),(27,true)]
theorem inp_495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_495 (by decide) v hb
def cl_496 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,false),(27,true)]
theorem inp_496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_496 v hb
def cl_497 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,true),(27,true)]
theorem inp_497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_497 (by decide) v hb
def cl_498 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,true),(27,true)]
theorem inp_498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_498 v hb
def cl_499 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,true),(27,true)]
theorem inp_499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_499 v hb
def cl_500 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,true),(27,true)]
theorem inp_500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_500 v hb
def cl_501 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,true),(27,true)]
theorem inp_501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_501 (by decide) v hb
def cl_502 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,true),(27,true)]
theorem inp_502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_502 v hb
def cl_503 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,true),(27,true)]
theorem inp_503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_503 v hb
def cl_504 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,false),(20,true),(27,true)]
theorem inp_504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_504 v hb
def cl_505 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,true),(27,true)]
theorem inp_505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_505 v hb
def cl_506 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,true),(27,true)]
theorem inp_506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_506 v hb
def cl_507 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,true),(27,true)]
theorem inp_507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_507 v hb
def cl_508 : CNF.NClause := [(69,false),(2,true),(9,true),(11,false),(18,true),(20,true),(27,true)]
theorem inp_508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_508 v hb
def cl_509 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,true),(27,true)]
theorem inp_509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_509 (by decide) v hb
def cl_510 : CNF.NClause := [(69,false),(2,true),(9,false),(11,true),(18,true),(20,true),(27,true)]
theorem inp_510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_510 v hb
end Percolation.NReplay
