import NInputs006
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_561 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,true),(28,true)]
theorem inp_561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_561 (by decide) v hb
def cl_562 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,true),(28,true)]
theorem inp_562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_562 v hb
def cl_563 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,true),(28,true)]
theorem inp_563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_563 (by decide) v hb
def cl_564 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,true),(28,true)]
theorem inp_564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_564 (by decide) v hb
def cl_565 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,true),(28,true)]
theorem inp_565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_565 v hb
def cl_566 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,true),(28,true)]
theorem inp_566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_566 v hb
def cl_567 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,true),(28,true)]
theorem inp_567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_567 (by decide) v hb
def cl_568 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,false),(20,true),(28,true)]
theorem inp_568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_568 (by decide) v hb
def cl_569 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,true),(28,true)]
theorem inp_569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_569 (by decide) v hb
def cl_570 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,true),(28,true)]
theorem inp_570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_570 v hb
def cl_571 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,true),(28,true)]
theorem inp_571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_571 (by decide) v hb
def cl_572 : CNF.NClause := [(70,false),(3,true),(6,true),(14,false),(17,true),(20,true),(28,true)]
theorem inp_572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_572 (by decide) v hb
def cl_573 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,true),(28,true)]
theorem inp_573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_573 v hb
def cl_574 : CNF.NClause := [(70,false),(3,true),(6,false),(14,true),(17,true),(20,true),(28,true)]
theorem inp_574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_574 (by decide) v hb
def cl_575 : CNF.NClause := [(70,false),(3,false),(6,true),(14,true),(17,true),(20,true),(28,true)]
theorem inp_575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_575 (by decide) v hb
def cl_577 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,false),(26,false)]
theorem inp_577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_577 v hb
def cl_578 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,false),(26,false)]
theorem inp_578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_578 v hb
def cl_579 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,false),(26,false)]
theorem inp_579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_579 v hb
def cl_580 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,false),(26,false)]
theorem inp_580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_580 v hb
def cl_581 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,false),(26,false)]
theorem inp_581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_581 (by decide) v hb
def cl_582 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,false),(26,false)]
theorem inp_582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_582 (by decide) v hb
def cl_583 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,false),(26,false)]
theorem inp_583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_583 v hb
def cl_584 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,false),(26,false)]
theorem inp_584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_584 v hb
def cl_585 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,false),(26,false)]
theorem inp_585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_585 v hb
def cl_586 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,false),(26,false)]
theorem inp_586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_586 (by decide) v hb
def cl_587 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,false),(26,false)]
theorem inp_587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_587 v hb
def cl_588 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,false),(26,false)]
theorem inp_588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_588 v hb
def cl_589 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,false),(26,false)]
theorem inp_589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_589 v hb
def cl_590 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,true),(20,false),(26,false)]
theorem inp_590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_590 v hb
def cl_591 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,false),(26,false)]
theorem inp_591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_591 v hb
def cl_592 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,true),(20,false),(26,false)]
theorem inp_592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_592 (by decide) v hb
def cl_593 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,true),(26,false)]
theorem inp_593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_593 (by decide) v hb
def cl_594 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,true),(26,false)]
theorem inp_594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_594 (by decide) v hb
def cl_595 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,true),(26,false)]
theorem inp_595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_595 v hb
def cl_596 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,true),(26,false)]
theorem inp_596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_596 v hb
def cl_597 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,true),(26,false)]
theorem inp_597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_597 (by decide) v hb
def cl_598 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,true),(26,false)]
theorem inp_598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_598 (by decide) v hb
def cl_599 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,true),(26,false)]
theorem inp_599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_599 v hb
def cl_600 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,true),(26,false)]
theorem inp_600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_600 (by decide) v hb
def cl_601 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,true),(26,false)]
theorem inp_601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_601 v hb
def cl_602 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,true),(26,false)]
theorem inp_602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_602 (by decide) v hb
def cl_603 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,true),(26,false)]
theorem inp_603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_603 v hb
def cl_604 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,true),(26,false)]
theorem inp_604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_604 v hb
def cl_605 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,true),(26,false)]
theorem inp_605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_605 (by decide) v hb
def cl_606 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,true),(20,true),(26,false)]
theorem inp_606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_606 (by decide) v hb
def cl_607 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,true),(26,false)]
theorem inp_607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_607 v hb
def cl_608 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,true),(26,false)]
theorem inp_608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_608 v hb
def cl_609 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,false),(26,true)]
theorem inp_609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_609 v hb
def cl_610 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,false),(26,true)]
theorem inp_610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_610 (by decide) v hb
def cl_611 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,false),(26,true)]
theorem inp_611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_611 v hb
end Percolation.NReplay
