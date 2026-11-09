import Inputs005
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_570 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,true),(28,true)]
theorem inp_570 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_570 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_570 (by decide) v h
def cl_573 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,true),(28,true)]
theorem inp_573 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_573 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_573 (by decide) v h
def cl_576 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,true),(20,true),(28,true)]
theorem inp_576 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_576 := by
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) cl_576 (by decide) v h
def cl_577 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,false),(26,false)]
theorem inp_577 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_577 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_577 (by decide) v h
def cl_578 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,false),(26,false)]
theorem inp_578 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_578 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_578 (by decide) v h
def cl_579 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,false),(26,false)]
theorem inp_579 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_579 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_579 (by decide) v h
def cl_580 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,false),(26,false)]
theorem inp_580 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_580 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_580 (by decide) v h
def cl_583 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,false),(26,false)]
theorem inp_583 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_583 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_583 (by decide) v h
def cl_584 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,false),(26,false)]
theorem inp_584 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_584 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_584 (by decide) v h
def cl_585 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,false),(26,false)]
theorem inp_585 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_585 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_585 (by decide) v h
def cl_587 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,false),(26,false)]
theorem inp_587 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_587 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_587 (by decide) v h
def cl_588 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,false),(26,false)]
theorem inp_588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_588 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_588 (by decide) v h
def cl_589 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,false),(26,false)]
theorem inp_589 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_589 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_589 (by decide) v h
def cl_590 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,true),(20,false),(26,false)]
theorem inp_590 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_590 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_590 (by decide) v h
def cl_591 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,false),(26,false)]
theorem inp_591 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_591 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_591 (by decide) v h
def cl_595 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,true),(26,false)]
theorem inp_595 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_595 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_595 (by decide) v h
def cl_596 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,true),(26,false)]
theorem inp_596 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_596 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_596 (by decide) v h
def cl_599 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,true),(26,false)]
theorem inp_599 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_599 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_599 (by decide) v h
def cl_601 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,true),(26,false)]
theorem inp_601 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_601 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_601 (by decide) v h
def cl_603 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,true),(26,false)]
theorem inp_603 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_603 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_603 (by decide) v h
def cl_604 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,true),(26,false)]
theorem inp_604 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_604 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_604 (by decide) v h
def cl_607 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,true),(26,false)]
theorem inp_607 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_607 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_607 (by decide) v h
def cl_608 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,true),(26,false)]
theorem inp_608 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_608 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_608 (by decide) v h
def cl_609 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,false),(26,true)]
theorem inp_609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_609 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_609 (by decide) v h
def cl_611 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,false),(26,true)]
theorem inp_611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_611 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_611 (by decide) v h
def cl_612 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,false),(26,true)]
theorem inp_612 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_612 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_612 (by decide) v h
def cl_615 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,false),(26,true)]
theorem inp_615 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_615 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_615 (by decide) v h
def cl_616 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,false),(26,true)]
theorem inp_616 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_616 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_616 (by decide) v h
def cl_617 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,false),(26,true)]
theorem inp_617 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_617 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_617 (by decide) v h
def cl_619 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,false),(26,true)]
theorem inp_619 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_619 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_619 (by decide) v h
def cl_620 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,false),(26,true)]
theorem inp_620 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_620 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_620 (by decide) v h
def cl_623 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,false),(26,true)]
theorem inp_623 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_623 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_623 (by decide) v h
def cl_624 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,false),(26,true)]
theorem inp_624 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_624 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_624 (by decide) v h
def cl_627 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,true),(26,true)]
theorem inp_627 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_627 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_627 (by decide) v h
def cl_628 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,true),(26,true)]
theorem inp_628 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_628 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_628 (by decide) v h
def cl_631 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,true),(26,true)]
theorem inp_631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_631 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_631 (by decide) v h
def cl_632 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,false),(20,true),(26,true)]
theorem inp_632 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_632 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_632 (by decide) v h
def cl_633 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,true),(26,true)]
theorem inp_633 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_633 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_633 (by decide) v h
def cl_635 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,true),(26,true)]
theorem inp_635 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_635 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_635 (by decide) v h
def cl_636 : CNF.NClause := [(71,false),(1,true),(7,true),(13,false),(19,true),(20,true),(26,true)]
theorem inp_636 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_636 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_636 (by decide) v h
def cl_638 : CNF.NClause := [(71,false),(1,true),(7,false),(13,true),(19,true),(20,true),(26,true)]
theorem inp_638 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_638 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_638 (by decide) v h
def cl_639 : CNF.NClause := [(71,false),(1,false),(7,true),(13,true),(19,true),(20,true),(26,true)]
theorem inp_639 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_639 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_639 (by decide) v h
def cl_640 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,true),(26,true)]
theorem inp_640 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_640 := by
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_640 (by decide) v h
def cl_641 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,false),(30,false)]
theorem inp_641 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_641 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_641 (by decide) v h
def cl_642 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,false),(30,false)]
theorem inp_642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_642 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_642 (by decide) v h
def cl_643 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,false),(14,false),(30,false)]
theorem inp_643 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_643 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_643 (by decide) v h
def cl_644 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,false),(14,false),(30,false)]
theorem inp_644 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_644 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_644 (by decide) v h
def cl_645 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,false),(30,false)]
theorem inp_645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_645 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_645 (by decide) v h
def cl_646 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,false),(30,false)]
theorem inp_646 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_646 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_646 (by decide) v h
def cl_647 : CNF.NClause := [(72,true),(10,false),(11,true),(12,true),(13,false),(14,false),(30,false)]
theorem inp_647 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_647 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_647 (by decide) v h
end Percolation.Replay
