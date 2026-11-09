import Inputs020
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1727 : CNF.NClause := [(88,false),(0,false),(9,true),(13,true),(17,true),(21,true),(29,true)]
theorem inp_1727 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1727 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1727 (by decide) v h
def cl_1728 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,true),(21,true),(29,true)]
theorem inp_1728 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1728 := by
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1728 (by decide) v h
def cl_1729 : CNF.NClause := [(89,true),(0,false),(7,false),(14,false),(16,false),(23,false),(27,false)]
theorem inp_1729 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1729 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1729 (by decide) v h
def cl_1730 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,false),(27,false)]
theorem inp_1730 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1730 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1730 (by decide) v h
def cl_1731 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,false),(23,false),(27,false)]
theorem inp_1731 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1731 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1731 (by decide) v h
def cl_1732 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,false),(27,false)]
theorem inp_1732 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1732 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1732 (by decide) v h
def cl_1735 : CNF.NClause := [(89,true),(0,false),(7,true),(14,true),(16,false),(23,false),(27,false)]
theorem inp_1735 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1735 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1735 (by decide) v h
def cl_1736 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,false),(27,false)]
theorem inp_1736 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1736 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1736 (by decide) v h
def cl_1739 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,true),(23,false),(27,false)]
theorem inp_1739 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1739 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1739 (by decide) v h
def cl_1743 : CNF.NClause := [(89,true),(0,false),(7,true),(14,true),(16,true),(23,false),(27,false)]
theorem inp_1743 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1743 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1743 (by decide) v h
def cl_1747 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,false),(23,true),(27,false)]
theorem inp_1747 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1747 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1747 (by decide) v h
def cl_1751 : CNF.NClause := [(89,true),(0,false),(7,true),(14,true),(16,false),(23,true),(27,false)]
theorem inp_1751 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1751 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1751 (by decide) v h
def cl_1752 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,true),(27,false)]
theorem inp_1752 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1752 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1752 (by decide) v h
def cl_1755 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,true),(23,true),(27,false)]
theorem inp_1755 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1755 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1755 (by decide) v h
def cl_1759 : CNF.NClause := [(89,true),(0,false),(7,true),(14,true),(16,true),(23,true),(27,false)]
theorem inp_1759 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1759 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1759 (by decide) v h
def cl_1760 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,true),(23,true),(27,false)]
theorem inp_1760 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1760 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1760 (by decide) v h
def cl_1761 : CNF.NClause := [(89,true),(0,false),(7,false),(14,false),(16,false),(23,false),(27,true)]
theorem inp_1761 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1761 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1761 (by decide) v h
def cl_1763 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,false),(23,false),(27,true)]
theorem inp_1763 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1763 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1763 (by decide) v h
def cl_1764 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,false),(27,true)]
theorem inp_1764 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1764 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1764 (by decide) v h
def cl_1767 : CNF.NClause := [(89,true),(0,false),(7,true),(14,true),(16,false),(23,false),(27,true)]
theorem inp_1767 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1767 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1767 (by decide) v h
def cl_1768 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,false),(27,true)]
theorem inp_1768 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1768 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1768 (by decide) v h
def cl_1771 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,true),(23,false),(27,true)]
theorem inp_1771 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1771 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1771 (by decide) v h
def cl_1772 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,true),(23,false),(27,true)]
theorem inp_1772 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1772 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1772 (by decide) v h
def cl_1775 : CNF.NClause := [(89,true),(0,false),(7,true),(14,true),(16,true),(23,false),(27,true)]
theorem inp_1775 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1775 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1775 (by decide) v h
def cl_1776 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,true),(23,false),(27,true)]
theorem inp_1776 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1776 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1776 (by decide) v h
def cl_1779 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,false),(23,true),(27,true)]
theorem inp_1779 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1779 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1779 (by decide) v h
def cl_1783 : CNF.NClause := [(89,true),(0,false),(7,true),(14,true),(16,false),(23,true),(27,true)]
theorem inp_1783 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1783 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1783 (by decide) v h
def cl_1784 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,false),(23,true),(27,true)]
theorem inp_1784 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1784 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1784 (by decide) v h
def cl_1787 : CNF.NClause := [(89,true),(0,false),(7,true),(14,false),(16,true),(23,true),(27,true)]
theorem inp_1787 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1787 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1787 (by decide) v h
def cl_1788 : CNF.NClause := [(89,false),(0,true),(7,true),(14,false),(16,true),(23,true),(27,true)]
theorem inp_1788 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1788 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1788 (by decide) v h
def cl_1790 : CNF.NClause := [(89,false),(0,true),(7,false),(14,true),(16,true),(23,true),(27,true)]
theorem inp_1790 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1790 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1790 (by decide) v h
def cl_1791 : CNF.NClause := [(89,false),(0,false),(7,true),(14,true),(16,true),(23,true),(27,true)]
theorem inp_1791 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1791 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1791 (by decide) v h
def cl_1792 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,true),(23,true),(27,true)]
theorem inp_1792 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1792 := by
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1792 (by decide) v h
def cl_1793 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(19,false),(22,false),(28,false)]
theorem inp_1793 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1793 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1793 (by decide) v h
def cl_1794 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,false),(28,false)]
theorem inp_1794 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1794 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1794 (by decide) v h
def cl_1795 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,false),(22,false),(28,false)]
theorem inp_1795 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1795 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1795 (by decide) v h
def cl_1796 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,false),(28,false)]
theorem inp_1796 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1796 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1796 (by decide) v h
def cl_1797 : CNF.NClause := [(90,true),(0,false),(8,false),(11,true),(19,false),(22,false),(28,false)]
theorem inp_1797 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1797 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1797 (by decide) v h
def cl_1798 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,false),(28,false)]
theorem inp_1798 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1798 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1798 (by decide) v h
def cl_1799 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,false),(22,false),(28,false)]
theorem inp_1799 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1799 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1799 (by decide) v h
def cl_1800 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,false),(28,false)]
theorem inp_1800 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1800 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1800 (by decide) v h
def cl_1801 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(19,true),(22,false),(28,false)]
theorem inp_1801 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1801 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1801 (by decide) v h
def cl_1802 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,false),(28,false)]
theorem inp_1802 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1802 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1802 (by decide) v h
def cl_1803 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,true),(22,false),(28,false)]
theorem inp_1803 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1803 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1803 (by decide) v h
def cl_1804 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,false),(28,false)]
theorem inp_1804 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1804 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1804 (by decide) v h
def cl_1806 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,false),(28,false)]
theorem inp_1806 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1806 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1806 (by decide) v h
def cl_1807 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,true),(22,false),(28,false)]
theorem inp_1807 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1807 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1807 (by decide) v h
def cl_1811 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,false),(22,true),(28,false)]
theorem inp_1811 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1811 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1811 (by decide) v h
def cl_1812 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,true),(28,false)]
theorem inp_1812 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1812 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1812 (by decide) v h
def cl_1815 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,false),(22,true),(28,false)]
theorem inp_1815 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1815 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1815 (by decide) v h
end Percolation.Replay
