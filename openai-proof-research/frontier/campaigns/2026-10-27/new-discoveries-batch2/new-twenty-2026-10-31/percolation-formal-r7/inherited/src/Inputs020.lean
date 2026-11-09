import Inputs019
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1660 : CNF.NClause := [(87,false),(0,true),(1,true),(2,false),(3,true),(4,true),(30,true)]
theorem inp_1660 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1660 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1660 (by decide) v h
def cl_1661 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,true),(4,true),(30,true)]
theorem inp_1661 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1661 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1661 (by decide) v h
def cl_1662 : CNF.NClause := [(87,false),(0,true),(1,false),(2,true),(3,true),(4,true),(30,true)]
theorem inp_1662 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1662 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1662 (by decide) v h
def cl_1663 : CNF.NClause := [(87,false),(0,false),(1,true),(2,true),(3,true),(4,true),(30,true)]
theorem inp_1663 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1663 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1663 (by decide) v h
def cl_1664 : CNF.NClause := [(87,false),(0,true),(1,true),(2,true),(3,true),(4,true),(30,true)]
theorem inp_1664 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1664 := by
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1664 (by decide) v h
def cl_1665 : CNF.NClause := [(88,true),(0,false),(9,false),(13,false),(17,false),(21,false),(29,false)]
theorem inp_1665 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1665 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1665 (by decide) v h
def cl_1666 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,false),(29,false)]
theorem inp_1666 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1666 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1666 (by decide) v h
def cl_1667 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,false),(21,false),(29,false)]
theorem inp_1667 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1667 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1667 (by decide) v h
def cl_1668 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,false),(29,false)]
theorem inp_1668 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1668 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1668 (by decide) v h
def cl_1671 : CNF.NClause := [(88,true),(0,false),(9,true),(13,true),(17,false),(21,false),(29,false)]
theorem inp_1671 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1671 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1671 (by decide) v h
def cl_1672 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,false),(29,false)]
theorem inp_1672 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1672 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1672 (by decide) v h
def cl_1673 : CNF.NClause := [(88,true),(0,false),(9,false),(13,false),(17,true),(21,false),(29,false)]
theorem inp_1673 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1673 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1673 (by decide) v h
def cl_1674 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,false),(29,false)]
theorem inp_1674 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1674 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1674 (by decide) v h
def cl_1675 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,true),(21,false),(29,false)]
theorem inp_1675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1675 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1675 (by decide) v h
def cl_1676 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,false),(29,false)]
theorem inp_1676 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1676 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1676 (by decide) v h
def cl_1679 : CNF.NClause := [(88,true),(0,false),(9,true),(13,true),(17,true),(21,false),(29,false)]
theorem inp_1679 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1679 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1679 (by decide) v h
def cl_1680 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,true),(21,false),(29,false)]
theorem inp_1680 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1680 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1680 (by decide) v h
def cl_1683 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,false),(21,true),(29,false)]
theorem inp_1683 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1683 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1683 (by decide) v h
def cl_1684 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,true),(29,false)]
theorem inp_1684 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1684 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1684 (by decide) v h
def cl_1687 : CNF.NClause := [(88,true),(0,false),(9,true),(13,true),(17,false),(21,true),(29,false)]
theorem inp_1687 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1687 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1687 (by decide) v h
def cl_1688 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,true),(29,false)]
theorem inp_1688 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1688 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1688 (by decide) v h
def cl_1689 : CNF.NClause := [(88,true),(0,false),(9,false),(13,false),(17,true),(21,true),(29,false)]
theorem inp_1689 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1689 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1689 (by decide) v h
def cl_1690 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,true),(29,false)]
theorem inp_1690 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1690 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1690 (by decide) v h
def cl_1691 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,true),(21,true),(29,false)]
theorem inp_1691 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1691 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1691 (by decide) v h
def cl_1692 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,true),(29,false)]
theorem inp_1692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1692 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1692 (by decide) v h
def cl_1695 : CNF.NClause := [(88,true),(0,false),(9,true),(13,true),(17,true),(21,true),(29,false)]
theorem inp_1695 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1695 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1695 (by decide) v h
def cl_1696 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,true),(21,true),(29,false)]
theorem inp_1696 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1696 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1696 (by decide) v h
def cl_1697 : CNF.NClause := [(88,true),(0,false),(9,false),(13,false),(17,false),(21,false),(29,true)]
theorem inp_1697 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1697 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1697 (by decide) v h
def cl_1698 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,false),(29,true)]
theorem inp_1698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1698 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1698 (by decide) v h
def cl_1699 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,false),(21,false),(29,true)]
theorem inp_1699 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1699 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1699 (by decide) v h
def cl_1700 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,false),(29,true)]
theorem inp_1700 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1700 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1700 (by decide) v h
def cl_1702 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,false),(29,true)]
theorem inp_1702 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1702 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1702 (by decide) v h
def cl_1703 : CNF.NClause := [(88,true),(0,false),(9,true),(13,true),(17,false),(21,false),(29,true)]
theorem inp_1703 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1703 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1703 (by decide) v h
def cl_1704 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,false),(29,true)]
theorem inp_1704 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1704 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1704 (by decide) v h
def cl_1705 : CNF.NClause := [(88,true),(0,false),(9,false),(13,false),(17,true),(21,false),(29,true)]
theorem inp_1705 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1705 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1705 (by decide) v h
def cl_1706 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,false),(29,true)]
theorem inp_1706 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1706 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1706 (by decide) v h
def cl_1707 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,true),(21,false),(29,true)]
theorem inp_1707 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1707 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1707 (by decide) v h
def cl_1708 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,false),(29,true)]
theorem inp_1708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1708 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1708 (by decide) v h
def cl_1710 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,true),(21,false),(29,true)]
theorem inp_1710 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1710 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1710 (by decide) v h
def cl_1711 : CNF.NClause := [(88,true),(0,false),(9,true),(13,true),(17,true),(21,false),(29,true)]
theorem inp_1711 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1711 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1711 (by decide) v h
def cl_1712 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,true),(21,false),(29,true)]
theorem inp_1712 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1712 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1712 (by decide) v h
def cl_1715 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,false),(21,true),(29,true)]
theorem inp_1715 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1715 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1715 (by decide) v h
def cl_1716 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,true),(29,true)]
theorem inp_1716 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1716 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1716 (by decide) v h
def cl_1719 : CNF.NClause := [(88,true),(0,false),(9,true),(13,true),(17,false),(21,true),(29,true)]
theorem inp_1719 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1719 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1719 (by decide) v h
def cl_1720 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,false),(21,true),(29,true)]
theorem inp_1720 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1720 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1720 (by decide) v h
def cl_1721 : CNF.NClause := [(88,true),(0,false),(9,false),(13,false),(17,true),(21,true),(29,true)]
theorem inp_1721 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1721 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1721 (by decide) v h
def cl_1722 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,true),(29,true)]
theorem inp_1722 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1722 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1722 (by decide) v h
def cl_1723 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,true),(21,true),(29,true)]
theorem inp_1723 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1723 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1723 (by decide) v h
def cl_1724 : CNF.NClause := [(88,false),(0,true),(9,true),(13,false),(17,true),(21,true),(29,true)]
theorem inp_1724 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1724 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1724 (by decide) v h
def cl_1726 : CNF.NClause := [(88,false),(0,true),(9,false),(13,true),(17,true),(21,true),(29,true)]
theorem inp_1726 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1726 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1726 (by decide) v h
end Percolation.Replay
