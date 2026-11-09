import Inputs003
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_416 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,true),(29,false)]
theorem inp_416 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_416 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_416 (by decide) v h
def cl_417 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,false),(29,true)]
theorem inp_417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_417 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_417 (by decide) v h
def cl_419 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,false),(29,true)]
theorem inp_419 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_419 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_419 (by decide) v h
def cl_420 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,false),(29,true)]
theorem inp_420 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_420 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_420 (by decide) v h
def cl_423 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,false),(29,true)]
theorem inp_423 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_423 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_423 (by decide) v h
def cl_424 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,false),(29,true)]
theorem inp_424 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_424 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_424 (by decide) v h
def cl_425 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,false),(29,true)]
theorem inp_425 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_425 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_425 (by decide) v h
def cl_426 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,false),(29,true)]
theorem inp_426 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_426 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_426 (by decide) v h
def cl_427 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,false),(29,true)]
theorem inp_427 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_427 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_427 (by decide) v h
def cl_428 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,false),(29,true)]
theorem inp_428 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_428 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_428 (by decide) v h
def cl_429 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,false),(29,true)]
theorem inp_429 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_429 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_429 (by decide) v h
def cl_431 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,false),(29,true)]
theorem inp_431 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_431 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_431 (by decide) v h
def cl_432 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,false),(29,true)]
theorem inp_432 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_432 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_432 (by decide) v h
def cl_433 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,true),(29,true)]
theorem inp_433 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_433 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_433 (by decide) v h
def cl_434 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,true),(29,true)]
theorem inp_434 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_434 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_434 (by decide) v h
def cl_435 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,true),(29,true)]
theorem inp_435 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_435 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_435 (by decide) v h
def cl_436 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,true),(29,true)]
theorem inp_436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_436 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_436 (by decide) v h
def cl_438 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,true),(29,true)]
theorem inp_438 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_438 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_438 (by decide) v h
def cl_439 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,true),(29,true)]
theorem inp_439 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_439 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_439 (by decide) v h
def cl_440 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,false),(20,true),(29,true)]
theorem inp_440 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_440 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_440 (by decide) v h
def cl_441 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,true),(29,true)]
theorem inp_441 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_441 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_441 (by decide) v h
def cl_442 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,true),(29,true)]
theorem inp_442 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_442 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_442 (by decide) v h
def cl_443 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,true),(29,true)]
theorem inp_443 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_443 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_443 (by decide) v h
def cl_444 : CNF.NClause := [(68,false),(4,true),(8,true),(12,false),(16,true),(20,true),(29,true)]
theorem inp_444 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_444 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_444 (by decide) v h
def cl_446 : CNF.NClause := [(68,false),(4,true),(8,false),(12,true),(16,true),(20,true),(29,true)]
theorem inp_446 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_446 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_446 (by decide) v h
def cl_447 : CNF.NClause := [(68,false),(4,false),(8,true),(12,true),(16,true),(20,true),(29,true)]
theorem inp_447 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_447 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_447 (by decide) v h
def cl_448 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,true),(29,true)]
theorem inp_448 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_448 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_448 (by decide) v h
def cl_449 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,false),(27,false)]
theorem inp_449 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_449 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_449 (by decide) v h
def cl_450 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,false),(27,false)]
theorem inp_450 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_450 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_450 (by decide) v h
def cl_451 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,false),(27,false)]
theorem inp_451 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_451 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_451 (by decide) v h
def cl_452 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,false),(27,false)]
theorem inp_452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_452 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_452 (by decide) v h
def cl_453 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,false),(27,false)]
theorem inp_453 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_453 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_453 (by decide) v h
def cl_454 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,false),(27,false)]
theorem inp_454 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_454 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_454 (by decide) v h
def cl_455 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,false),(27,false)]
theorem inp_455 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_455 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_455 (by decide) v h
def cl_456 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,false),(27,false)]
theorem inp_456 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_456 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_456 (by decide) v h
def cl_457 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,false),(27,false)]
theorem inp_457 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_457 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_457 (by decide) v h
def cl_458 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,false),(27,false)]
theorem inp_458 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_458 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_458 (by decide) v h
def cl_459 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,false),(27,false)]
theorem inp_459 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_459 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_459 (by decide) v h
def cl_467 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,true),(27,false)]
theorem inp_467 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_467 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_467 (by decide) v h
def cl_473 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,true),(27,false)]
theorem inp_473 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_473 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_473 (by decide) v h
def cl_474 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,true),(27,false)]
theorem inp_474 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_474 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_474 (by decide) v h
def cl_475 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,true),(27,false)]
theorem inp_475 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_475 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_475 (by decide) v h
def cl_480 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,true),(27,false)]
theorem inp_480 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_480 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_480 (by decide) v h
def cl_481 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,false),(20,false),(27,true)]
theorem inp_481 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_481 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_481 (by decide) v h
def cl_482 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,false),(27,true)]
theorem inp_482 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_482 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_482 (by decide) v h
def cl_483 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,false),(27,true)]
theorem inp_483 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_483 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_483 (by decide) v h
def cl_484 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,false),(27,true)]
theorem inp_484 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_484 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_484 (by decide) v h
def cl_486 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,false),(27,true)]
theorem inp_486 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_486 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_486 (by decide) v h
def cl_487 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,false),(27,true)]
theorem inp_487 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_487 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_487 (by decide) v h
def cl_488 : CNF.NClause := [(69,true),(2,true),(9,true),(11,true),(18,false),(20,false),(27,true)]
theorem inp_488 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_488 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_488 (by decide) v h
end Percolation.Replay
