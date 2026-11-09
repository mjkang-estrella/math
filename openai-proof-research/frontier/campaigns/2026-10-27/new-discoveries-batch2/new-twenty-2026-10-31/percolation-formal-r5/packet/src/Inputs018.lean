import Inputs017
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1484 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,false),(27,false)]
theorem inp_1484 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1484 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1484 (by decide) v h
def cl_1487 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,false),(27,false)]
theorem inp_1487 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1487 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1487 (by decide) v h
def cl_1491 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,true),(27,false)]
theorem inp_1491 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1491 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1491 (by decide) v h
def cl_1492 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,true),(27,false)]
theorem inp_1492 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1492 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1492 (by decide) v h
def cl_1495 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,true),(27,false)]
theorem inp_1495 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1495 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1495 (by decide) v h
def cl_1499 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,true),(27,false)]
theorem inp_1499 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1499 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1499 (by decide) v h
def cl_1500 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,true),(27,false)]
theorem inp_1500 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1500 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1500 (by decide) v h
def cl_1503 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,true),(27,false)]
theorem inp_1503 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1503 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1503 (by decide) v h
def cl_1505 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,false),(27,true)]
theorem inp_1505 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1505 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1505 (by decide) v h
def cl_1507 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,false),(27,true)]
theorem inp_1507 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1507 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1507 (by decide) v h
def cl_1508 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,false),(27,true)]
theorem inp_1508 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1508 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1508 (by decide) v h
def cl_1511 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,false),(27,true)]
theorem inp_1511 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1511 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1511 (by decide) v h
def cl_1512 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,false),(21,false),(27,true)]
theorem inp_1512 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1512 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1512 (by decide) v h
def cl_1515 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,false),(27,true)]
theorem inp_1515 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1515 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1515 (by decide) v h
def cl_1516 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,false),(27,true)]
theorem inp_1516 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1516 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1516 (by decide) v h
def cl_1519 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,false),(27,true)]
theorem inp_1519 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1519 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1519 (by decide) v h
def cl_1523 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,true),(27,true)]
theorem inp_1523 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1523 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1523 (by decide) v h
def cl_1524 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,true),(27,true)]
theorem inp_1524 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1524 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1524 (by decide) v h
def cl_1527 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,true),(27,true)]
theorem inp_1527 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1527 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1527 (by decide) v h
def cl_1531 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,true),(27,true)]
theorem inp_1531 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1531 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1531 (by decide) v h
def cl_1537 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1537 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1537 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1537 (by decide) v h
def cl_1538 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1538 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1538 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1538 (by decide) v h
def cl_1539 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1539 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1539 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1539 (by decide) v h
def cl_1540 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1540 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1540 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1540 (by decide) v h
def cl_1543 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,false),(29,false)]
theorem inp_1543 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1543 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1543 (by decide) v h
def cl_1544 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,false),(29,false)]
theorem inp_1544 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1544 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1544 (by decide) v h
def cl_1547 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,false),(29,false)]
theorem inp_1547 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1547 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1547 (by decide) v h
def cl_1548 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,false),(29,false)]
theorem inp_1548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1548 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1548 (by decide) v h
def cl_1551 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,false),(29,false)]
theorem inp_1551 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1551 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1551 (by decide) v h
def cl_1552 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,true),(22,false),(29,false)]
theorem inp_1552 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1552 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1552 (by decide) v h
def cl_1555 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,true),(29,false)]
theorem inp_1555 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1555 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1555 (by decide) v h
def cl_1559 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,true),(29,false)]
theorem inp_1559 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1559 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1559 (by decide) v h
def cl_1560 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,true),(29,false)]
theorem inp_1560 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1560 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1560 (by decide) v h
def cl_1563 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,true),(29,false)]
theorem inp_1563 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1563 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1563 (by decide) v h
def cl_1567 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,true),(29,false)]
theorem inp_1567 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1567 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1567 (by decide) v h
def cl_1569 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,false),(29,true)]
theorem inp_1569 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1569 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1569 (by decide) v h
def cl_1571 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,false),(29,true)]
theorem inp_1571 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1571 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1571 (by decide) v h
def cl_1572 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,false),(29,true)]
theorem inp_1572 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1572 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1572 (by decide) v h
def cl_1575 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,false),(29,true)]
theorem inp_1575 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1575 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1575 (by decide) v h
def cl_1576 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,false),(29,true)]
theorem inp_1576 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1576 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1576 (by decide) v h
def cl_1579 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,false),(29,true)]
theorem inp_1579 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1579 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1579 (by decide) v h
def cl_1580 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,false),(29,true)]
theorem inp_1580 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1580 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1580 (by decide) v h
def cl_1583 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,false),(29,true)]
theorem inp_1583 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1583 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1583 (by decide) v h
def cl_1587 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,true),(29,true)]
theorem inp_1587 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1587 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1587 (by decide) v h
def cl_1591 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,true),(29,true)]
theorem inp_1591 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1591 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1591 (by decide) v h
def cl_1595 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,true),(29,true)]
theorem inp_1595 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1595 := by
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1595 (by decide) v h
def cl_1601 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,false),(4,false),(30,false)]
theorem inp_1601 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1601 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1601 (by decide) v h
def cl_1602 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,false),(30,false)]
theorem inp_1602 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1602 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1602 (by decide) v h
def cl_1603 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,false),(4,false),(30,false)]
theorem inp_1603 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1603 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1603 (by decide) v h
def cl_1604 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,false),(4,false),(30,false)]
theorem inp_1604 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1604 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1604 (by decide) v h
end Percolation.Replay
