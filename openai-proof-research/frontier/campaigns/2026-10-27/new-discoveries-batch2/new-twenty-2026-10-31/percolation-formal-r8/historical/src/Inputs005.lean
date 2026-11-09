import Inputs004
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_489 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,false),(27,true)]
theorem inp_489 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_489 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_489 (by decide) v h
def cl_490 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,false),(27,true)]
theorem inp_490 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_490 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_490 (by decide) v h
def cl_491 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,false),(27,true)]
theorem inp_491 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_491 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_491 (by decide) v h
def cl_492 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,true),(20,false),(27,true)]
theorem inp_492 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_492 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_492 (by decide) v h
def cl_496 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,false),(27,true)]
theorem inp_496 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_496 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_496 (by decide) v h
def cl_498 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,true),(27,true)]
theorem inp_498 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_498 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_498 (by decide) v h
def cl_499 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,true),(27,true)]
theorem inp_499 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_499 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_499 (by decide) v h
def cl_500 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,true),(27,true)]
theorem inp_500 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_500 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_500 (by decide) v h
def cl_502 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,true),(27,true)]
theorem inp_502 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_502 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_502 (by decide) v h
def cl_503 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,true),(27,true)]
theorem inp_503 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_503 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_503 (by decide) v h
def cl_504 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,false),(20,true),(27,true)]
theorem inp_504 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_504 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_504 (by decide) v h
def cl_505 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,true),(27,true)]
theorem inp_505 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_505 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_505 (by decide) v h
def cl_506 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,true),(27,true)]
theorem inp_506 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_506 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_506 (by decide) v h
def cl_507 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,true),(27,true)]
theorem inp_507 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_507 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_507 (by decide) v h
def cl_508 : CNF.NClause := [(69,false),(2,true),(9,true),(11,false),(18,true),(20,true),(27,true)]
theorem inp_508 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_508 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_508 (by decide) v h
def cl_510 : CNF.NClause := [(69,false),(2,true),(9,false),(11,true),(18,true),(20,true),(27,true)]
theorem inp_510 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_510 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_510 (by decide) v h
def cl_511 : CNF.NClause := [(69,false),(2,false),(9,true),(11,true),(18,true),(20,true),(27,true)]
theorem inp_511 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_511 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_511 (by decide) v h
def cl_512 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,true),(27,true)]
theorem inp_512 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_512 := by
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) cl_512 (by decide) v h
def cl_513 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,false),(28,false)]
theorem inp_513 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_513 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_513 (by decide) v h
def cl_514 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,false),(28,false)]
theorem inp_514 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_514 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_514 (by decide) v h
def cl_515 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,false),(28,false)]
theorem inp_515 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_515 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_515 (by decide) v h
def cl_516 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,false),(28,false)]
theorem inp_516 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_516 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_516 (by decide) v h
def cl_517 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,false),(28,false)]
theorem inp_517 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_517 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_517 (by decide) v h
def cl_518 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,false),(28,false)]
theorem inp_518 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_518 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_518 (by decide) v h
def cl_522 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,false),(28,false)]
theorem inp_522 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_522 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_522 (by decide) v h
def cl_525 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,false),(28,false)]
theorem inp_525 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_525 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_525 (by decide) v h
def cl_526 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,false),(28,false)]
theorem inp_526 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_526 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_526 (by decide) v h
def cl_530 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,true),(28,false)]
theorem inp_530 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_530 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_530 (by decide) v h
def cl_531 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,true),(28,false)]
theorem inp_531 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_531 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_531 (by decide) v h
def cl_532 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,true),(28,false)]
theorem inp_532 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_532 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_532 (by decide) v h
def cl_533 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,true),(28,false)]
theorem inp_533 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_533 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_533 (by decide) v h
def cl_534 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,true),(28,false)]
theorem inp_534 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_534 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_534 (by decide) v h
def cl_538 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,true),(28,false)]
theorem inp_538 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_538 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_538 (by decide) v h
def cl_541 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,true),(28,false)]
theorem inp_541 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_541 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_541 (by decide) v h
def cl_542 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,true),(28,false)]
theorem inp_542 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_542 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_542 (by decide) v h
def cl_544 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,true),(20,true),(28,false)]
theorem inp_544 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_544 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_544 (by decide) v h
def cl_545 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,false),(28,true)]
theorem inp_545 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_545 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_545 (by decide) v h
def cl_546 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,false),(28,true)]
theorem inp_546 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_546 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_546 (by decide) v h
def cl_548 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,false),(28,true)]
theorem inp_548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_548 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_548 (by decide) v h
def cl_549 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,false),(28,true)]
theorem inp_549 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_549 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_549 (by decide) v h
def cl_550 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,false),(28,true)]
theorem inp_550 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_550 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_550 (by decide) v h
def cl_551 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,false),(28,true)]
theorem inp_551 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_551 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_551 (by decide) v h
def cl_554 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,false),(28,true)]
theorem inp_554 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_554 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_554 (by decide) v h
def cl_555 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,false),(28,true)]
theorem inp_555 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_555 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_555 (by decide) v h
def cl_557 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,false),(28,true)]
theorem inp_557 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_557 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_557 (by decide) v h
def cl_558 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,false),(28,true)]
theorem inp_558 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_558 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_558 (by decide) v h
def cl_559 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,true),(20,false),(28,true)]
theorem inp_559 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_559 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_559 (by decide) v h
def cl_562 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,true),(28,true)]
theorem inp_562 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_562 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_562 (by decide) v h
def cl_565 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,true),(28,true)]
theorem inp_565 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_565 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_565 (by decide) v h
def cl_566 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,true),(28,true)]
theorem inp_566 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_566 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_566 (by decide) v h
end Percolation.Replay
