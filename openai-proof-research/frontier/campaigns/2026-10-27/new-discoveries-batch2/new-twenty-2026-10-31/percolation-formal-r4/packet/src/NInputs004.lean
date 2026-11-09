import NInputs003
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_411 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,true),(29,false)]
theorem inp_411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_411 v hb
def cl_412 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,true),(29,false)]
theorem inp_412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_412 v hb
def cl_413 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,true),(29,false)]
theorem inp_413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_413 (by decide) v hb
def cl_414 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,true),(20,true),(29,false)]
theorem inp_414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_414 (by decide) v hb
def cl_415 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,true),(29,false)]
theorem inp_415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_415 v hb
def cl_416 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,true),(29,false)]
theorem inp_416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_416 v hb
def cl_417 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,false),(29,true)]
theorem inp_417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_417 v hb
def cl_418 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,false),(29,true)]
theorem inp_418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_418 (by decide) v hb
def cl_419 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,false),(29,true)]
theorem inp_419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_419 v hb
def cl_420 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,false),(29,true)]
theorem inp_420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_420 v hb
def cl_421 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,false),(29,true)]
theorem inp_421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_421 (by decide) v hb
def cl_422 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,false),(29,true)]
theorem inp_422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_422 (by decide) v hb
def cl_423 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,false),(29,true)]
theorem inp_423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_423 v hb
def cl_424 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,false),(29,true)]
theorem inp_424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_424 v hb
def cl_425 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,false),(29,true)]
theorem inp_425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_425 v hb
def cl_426 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,false),(29,true)]
theorem inp_426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_426 v hb
def cl_427 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,false),(29,true)]
theorem inp_427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_427 v hb
def cl_428 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,false),(29,true)]
theorem inp_428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_428 v hb
def cl_429 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,false),(29,true)]
theorem inp_429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_429 v hb
def cl_430 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,true),(20,false),(29,true)]
theorem inp_430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_430 (by decide) v hb
def cl_431 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,false),(29,true)]
theorem inp_431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_431 v hb
def cl_432 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,false),(29,true)]
theorem inp_432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_432 v hb
def cl_433 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,true),(29,true)]
theorem inp_433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_433 v hb
def cl_434 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,true),(29,true)]
theorem inp_434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_434 v hb
def cl_435 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,true),(29,true)]
theorem inp_435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_435 v hb
def cl_436 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,true),(29,true)]
theorem inp_436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_436 v hb
def cl_437 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,true),(29,true)]
theorem inp_437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_437 (by decide) v hb
def cl_438 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,true),(29,true)]
theorem inp_438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_438 v hb
def cl_439 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,true),(29,true)]
theorem inp_439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_439 v hb
def cl_440 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,false),(20,true),(29,true)]
theorem inp_440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_440 v hb
def cl_441 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,true),(29,true)]
theorem inp_441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_441 v hb
def cl_442 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,true),(29,true)]
theorem inp_442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_442 v hb
def cl_443 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,true),(29,true)]
theorem inp_443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_443 v hb
def cl_444 : CNF.NClause := [(68,false),(4,true),(8,true),(12,false),(16,true),(20,true),(29,true)]
theorem inp_444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_444 v hb
def cl_445 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,true),(29,true)]
theorem inp_445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_445 (by decide) v hb
def cl_446 : CNF.NClause := [(68,false),(4,true),(8,false),(12,true),(16,true),(20,true),(29,true)]
theorem inp_446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_446 v hb
def cl_447 : CNF.NClause := [(68,false),(4,false),(8,true),(12,true),(16,true),(20,true),(29,true)]
theorem inp_447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_447 v hb
def cl_448 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,true),(29,true)]
theorem inp_448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_448 v hb
def cl_449 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,false),(27,false)]
theorem inp_449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_449 v hb
def cl_450 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,false),(27,false)]
theorem inp_450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_450 v hb
def cl_451 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,false),(27,false)]
theorem inp_451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_451 v hb
def cl_452 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,false),(27,false)]
theorem inp_452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_452 v hb
def cl_453 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,false),(27,false)]
theorem inp_453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_453 v hb
def cl_454 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,false),(27,false)]
theorem inp_454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_454 v hb
def cl_455 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,false),(27,false)]
theorem inp_455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_455 v hb
def cl_456 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,false),(27,false)]
theorem inp_456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_456 v hb
def cl_457 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,false),(27,false)]
theorem inp_457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_457 v hb
def cl_458 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,false),(27,false)]
theorem inp_458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_458 v hb
def cl_459 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,false),(27,false)]
theorem inp_459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_459 v hb
def cl_460 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,true),(20,false),(27,false)]
theorem inp_460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_460 (by decide) v hb
end Percolation.NReplay
