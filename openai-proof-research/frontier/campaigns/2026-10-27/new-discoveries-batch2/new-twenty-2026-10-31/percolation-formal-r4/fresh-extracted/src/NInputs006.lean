import NInputs005
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_511 : CNF.NClause := [(69,false),(2,false),(9,true),(11,true),(18,true),(20,true),(27,true)]
theorem inp_511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_511 v hb
def cl_512 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,true),(27,true)]
theorem inp_512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_512 v hb
def cl_513 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,false),(28,false)]
theorem inp_513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_513 v hb
def cl_514 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,false),(28,false)]
theorem inp_514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_514 v hb
def cl_515 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,false),(28,false)]
theorem inp_515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_515 v hb
def cl_516 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,false),(28,false)]
theorem inp_516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_516 v hb
def cl_517 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,false),(28,false)]
theorem inp_517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_517 v hb
def cl_518 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,false),(28,false)]
theorem inp_518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_518 v hb
def cl_519 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,false),(28,false)]
theorem inp_519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_519 (by decide) v hb
def cl_520 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,false),(20,false),(28,false)]
theorem inp_520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_520 (by decide) v hb
def cl_521 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,false),(28,false)]
theorem inp_521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_521 (by decide) v hb
def cl_522 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,false),(28,false)]
theorem inp_522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_522 v hb
def cl_523 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,false),(28,false)]
theorem inp_523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_523 (by decide) v hb
def cl_524 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,true),(20,false),(28,false)]
theorem inp_524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_524 (by decide) v hb
def cl_525 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,false),(28,false)]
theorem inp_525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_525 v hb
def cl_526 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,false),(28,false)]
theorem inp_526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_526 v hb
def cl_527 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,true),(20,false),(28,false)]
theorem inp_527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_527 (by decide) v hb
def cl_528 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,true),(20,false),(28,false)]
theorem inp_528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_528 (by decide) v hb
def cl_529 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,true),(28,false)]
theorem inp_529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_529 (by decide) v hb
def cl_530 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,true),(28,false)]
theorem inp_530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_530 v hb
def cl_531 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,true),(28,false)]
theorem inp_531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_531 v hb
def cl_532 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,true),(28,false)]
theorem inp_532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_532 v hb
def cl_533 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,true),(28,false)]
theorem inp_533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_533 v hb
def cl_534 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,true),(28,false)]
theorem inp_534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_534 v hb
def cl_535 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,true),(28,false)]
theorem inp_535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_535 (by decide) v hb
def cl_536 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,false),(20,true),(28,false)]
theorem inp_536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_536 (by decide) v hb
def cl_537 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,true),(28,false)]
theorem inp_537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_537 (by decide) v hb
def cl_538 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,true),(28,false)]
theorem inp_538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_538 v hb
def cl_539 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,true),(28,false)]
theorem inp_539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_539 (by decide) v hb
def cl_540 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,true),(20,true),(28,false)]
theorem inp_540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_540 (by decide) v hb
def cl_541 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,true),(28,false)]
theorem inp_541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_541 v hb
def cl_542 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,true),(28,false)]
theorem inp_542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_542 v hb
def cl_543 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,true),(20,true),(28,false)]
theorem inp_543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_543 (by decide) v hb
def cl_544 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,true),(20,true),(28,false)]
theorem inp_544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_544 v hb
def cl_545 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,false),(28,true)]
theorem inp_545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_545 v hb
def cl_546 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,false),(28,true)]
theorem inp_546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_546 v hb
def cl_547 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,false),(28,true)]
theorem inp_547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_547 (by decide) v hb
def cl_548 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,false),(28,true)]
theorem inp_548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_548 v hb
def cl_549 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,false),(28,true)]
theorem inp_549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_549 v hb
def cl_550 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,false),(28,true)]
theorem inp_550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_550 v hb
def cl_551 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,false),(28,true)]
theorem inp_551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_551 v hb
def cl_552 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,false),(20,false),(28,true)]
theorem inp_552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_552 (by decide) v hb
def cl_553 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,false),(28,true)]
theorem inp_553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_553 (by decide) v hb
def cl_554 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,false),(28,true)]
theorem inp_554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_554 v hb
def cl_555 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,false),(28,true)]
theorem inp_555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_555 v hb
def cl_556 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,true),(20,false),(28,true)]
theorem inp_556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_556 (by decide) v hb
def cl_557 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,false),(28,true)]
theorem inp_557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_557 v hb
def cl_558 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,false),(28,true)]
theorem inp_558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_558 v hb
def cl_559 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,true),(20,false),(28,true)]
theorem inp_559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_559 v hb
def cl_560 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,true),(20,false),(28,true)]
theorem inp_560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_560 (by decide) v hb
end Percolation.NReplay
