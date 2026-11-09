import Inputs018
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1605 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,false),(4,false),(30,false)]
theorem inp_1605 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1605 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1605 (by decide) v h
def cl_1606 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,false),(4,false),(30,false)]
theorem inp_1606 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1606 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1606 (by decide) v h
def cl_1607 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,false),(4,false),(30,false)]
theorem inp_1607 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1607 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1607 (by decide) v h
def cl_1608 : CNF.NClause := [(87,true),(0,true),(1,true),(2,true),(3,false),(4,false),(30,false)]
theorem inp_1608 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1608 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1608 (by decide) v h
def cl_1609 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,true),(4,false),(30,false)]
theorem inp_1609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1609 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1609 (by decide) v h
def cl_1610 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,false),(30,false)]
theorem inp_1610 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1610 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1610 (by decide) v h
def cl_1611 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,true),(4,false),(30,false)]
theorem inp_1611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1611 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1611 (by decide) v h
def cl_1612 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,true),(4,false),(30,false)]
theorem inp_1612 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1612 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1612 (by decide) v h
def cl_1613 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,true),(4,false),(30,false)]
theorem inp_1613 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1613 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1613 (by decide) v h
def cl_1614 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,true),(4,false),(30,false)]
theorem inp_1614 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1614 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1614 (by decide) v h
def cl_1615 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,true),(4,false),(30,false)]
theorem inp_1615 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1615 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1615 (by decide) v h
def cl_1616 : CNF.NClause := [(87,true),(0,true),(1,true),(2,true),(3,true),(4,false),(30,false)]
theorem inp_1616 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1616 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1616 (by decide) v h
def cl_1617 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,false),(4,true),(30,false)]
theorem inp_1617 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1617 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1617 (by decide) v h
def cl_1618 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,true),(30,false)]
theorem inp_1618 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1618 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1618 (by decide) v h
def cl_1619 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,false),(4,true),(30,false)]
theorem inp_1619 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1619 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1619 (by decide) v h
def cl_1620 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,false),(4,true),(30,false)]
theorem inp_1620 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1620 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1620 (by decide) v h
def cl_1621 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,false),(4,true),(30,false)]
theorem inp_1621 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1621 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1621 (by decide) v h
def cl_1622 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,false),(4,true),(30,false)]
theorem inp_1622 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1622 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1622 (by decide) v h
def cl_1623 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,false),(4,true),(30,false)]
theorem inp_1623 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1623 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1623 (by decide) v h
def cl_1624 : CNF.NClause := [(87,true),(0,true),(1,true),(2,true),(3,false),(4,true),(30,false)]
theorem inp_1624 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1624 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1624 (by decide) v h
def cl_1625 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,true),(4,true),(30,false)]
theorem inp_1625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1625 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1625 (by decide) v h
def cl_1626 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,true),(30,false)]
theorem inp_1626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1626 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1626 (by decide) v h
def cl_1627 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,true),(4,true),(30,false)]
theorem inp_1627 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1627 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1627 (by decide) v h
def cl_1628 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,true),(4,true),(30,false)]
theorem inp_1628 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1628 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1628 (by decide) v h
def cl_1629 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,true),(4,true),(30,false)]
theorem inp_1629 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1629 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1629 (by decide) v h
def cl_1630 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,true),(4,true),(30,false)]
theorem inp_1630 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1630 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1630 (by decide) v h
def cl_1631 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,true),(4,true),(30,false)]
theorem inp_1631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1631 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1631 (by decide) v h
def cl_1633 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,false),(4,false),(30,true)]
theorem inp_1633 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1633 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1633 (by decide) v h
def cl_1634 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,false),(30,true)]
theorem inp_1634 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1634 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1634 (by decide) v h
def cl_1635 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,false),(4,false),(30,true)]
theorem inp_1635 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1635 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1635 (by decide) v h
def cl_1637 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,false),(4,false),(30,true)]
theorem inp_1637 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1637 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1637 (by decide) v h
def cl_1638 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,false),(4,false),(30,true)]
theorem inp_1638 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1638 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1638 (by decide) v h
def cl_1639 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,false),(4,false),(30,true)]
theorem inp_1639 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1639 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1639 (by decide) v h
def cl_1641 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,true),(4,false),(30,true)]
theorem inp_1641 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1641 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1641 (by decide) v h
def cl_1642 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,false),(30,true)]
theorem inp_1642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1642 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1642 (by decide) v h
def cl_1643 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,true),(4,false),(30,true)]
theorem inp_1643 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1643 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1643 (by decide) v h
def cl_1644 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,true),(4,false),(30,true)]
theorem inp_1644 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1644 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1644 (by decide) v h
def cl_1645 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,true),(4,false),(30,true)]
theorem inp_1645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1645 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1645 (by decide) v h
def cl_1646 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,true),(4,false),(30,true)]
theorem inp_1646 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1646 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1646 (by decide) v h
def cl_1647 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,true),(4,false),(30,true)]
theorem inp_1647 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1647 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1647 (by decide) v h
def cl_1648 : CNF.NClause := [(87,false),(0,true),(1,true),(2,true),(3,true),(4,false),(30,true)]
theorem inp_1648 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1648 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1648 (by decide) v h
def cl_1649 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,false),(4,true),(30,true)]
theorem inp_1649 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1649 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1649 (by decide) v h
def cl_1650 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,true),(30,true)]
theorem inp_1650 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1650 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1650 (by decide) v h
def cl_1651 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,false),(4,true),(30,true)]
theorem inp_1651 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1651 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1651 (by decide) v h
def cl_1653 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,false),(4,true),(30,true)]
theorem inp_1653 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1653 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1653 (by decide) v h
def cl_1655 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,false),(4,true),(30,true)]
theorem inp_1655 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1655 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1655 (by decide) v h
def cl_1656 : CNF.NClause := [(87,false),(0,true),(1,true),(2,true),(3,false),(4,true),(30,true)]
theorem inp_1656 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1656 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1656 (by decide) v h
def cl_1657 : CNF.NClause := [(87,true),(0,false),(1,false),(2,false),(3,true),(4,true),(30,true)]
theorem inp_1657 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1657 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1657 (by decide) v h
def cl_1658 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,true),(30,true)]
theorem inp_1658 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1658 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1658 (by decide) v h
def cl_1659 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,true),(4,true),(30,true)]
theorem inp_1659 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1659 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1659 (by decide) v h
end Percolation.Replay
