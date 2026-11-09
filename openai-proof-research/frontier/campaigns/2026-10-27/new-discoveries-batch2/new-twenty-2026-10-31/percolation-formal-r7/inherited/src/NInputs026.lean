import NInputs025
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1654 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,false),(4,true),(30,true)]
theorem inp_1654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1654 (by decide) v hb
def cl_1656 : CNF.NClause := [(87,false),(0,true),(1,true),(2,true),(3,false),(4,true),(30,true)]
theorem inp_1656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1656 v hb
def cl_1658 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,true),(30,true)]
theorem inp_1658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1658 v hb
def cl_1660 : CNF.NClause := [(87,false),(0,true),(1,true),(2,false),(3,true),(4,true),(30,true)]
theorem inp_1660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1660 v hb
def cl_1662 : CNF.NClause := [(87,false),(0,true),(1,false),(2,true),(3,true),(4,true),(30,true)]
theorem inp_1662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1662 v hb
def cl_1666 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,false),(29,false)]
theorem inp_1666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1666 v hb
def cl_1668 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,false),(29,false)]
theorem inp_1668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1668 v hb
def cl_1670 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,false),(29,false)]
theorem inp_1670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1670 (by decide) v hb
def cl_1672 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,false),(29,false)]
theorem inp_1672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1672 v hb
def cl_1674 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,false),(29,false)]
theorem inp_1674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1674 v hb
def cl_1676 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,false),(29,false)]
theorem inp_1676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1676 v hb
def cl_1678 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,true),(21,false),(29,false)]
theorem inp_1678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1678 (by decide) v hb
def cl_1680 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,true),(21,false),(29,false)]
theorem inp_1680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1680 v hb
def cl_1682 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,true),(29,false)]
theorem inp_1682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1682 (by decide) v hb
def cl_1684 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,true),(29,false)]
theorem inp_1684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1684 v hb
def cl_1686 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,true),(29,false)]
theorem inp_1686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1686 (by decide) v hb
def cl_1688 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,true),(29,false)]
theorem inp_1688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1688 v hb
def cl_1690 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,true),(29,false)]
theorem inp_1690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1690 v hb
def cl_1692 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,true),(29,false)]
theorem inp_1692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1692 v hb
def cl_1694 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,true),(21,true),(29,false)]
theorem inp_1694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1694 (by decide) v hb
def cl_1696 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,true),(21,true),(29,false)]
theorem inp_1696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1696 v hb
def cl_1698 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,false),(29,true)]
theorem inp_1698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1698 v hb
def cl_1700 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,false),(29,true)]
theorem inp_1700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1700 v hb
def cl_1702 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,false),(29,true)]
theorem inp_1702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1702 v hb
def cl_1704 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,false),(29,true)]
theorem inp_1704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1704 v hb
def cl_1706 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,false),(29,true)]
theorem inp_1706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1706 v hb
def cl_1708 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,false),(29,true)]
theorem inp_1708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1708 v hb
def cl_1710 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,true),(21,false),(29,true)]
theorem inp_1710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1710 v hb
def cl_1712 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,true),(21,false),(29,true)]
theorem inp_1712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1712 v hb
def cl_1714 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,true),(29,true)]
theorem inp_1714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1714 (by decide) v hb
def cl_1716 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,true),(29,true)]
theorem inp_1716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1716 v hb
def cl_1718 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,true),(29,true)]
theorem inp_1718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) cl_1718 (by decide) v hb
def cl_1720 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,false),(21,true),(29,true)]
theorem inp_1720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1720 v hb
def cl_1722 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,true),(29,true)]
theorem inp_1722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1722 v hb
def cl_1724 : CNF.NClause := [(88,false),(0,true),(9,true),(13,false),(17,true),(21,true),(29,true)]
theorem inp_1724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1724 v hb
def cl_1726 : CNF.NClause := [(88,false),(0,true),(9,false),(13,true),(17,true),(21,true),(29,true)]
theorem inp_1726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1726 v hb
def cl_1730 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,false),(27,false)]
theorem inp_1730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1730 v hb
def cl_1732 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,false),(27,false)]
theorem inp_1732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1732 v hb
def cl_1734 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,false),(27,false)]
theorem inp_1734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1734 (by decide) v hb
def cl_1736 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,false),(27,false)]
theorem inp_1736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1736 v hb
def cl_1738 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,false),(27,false)]
theorem inp_1738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1738 (by decide) v hb
def cl_1740 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,true),(23,false),(27,false)]
theorem inp_1740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1740 (by decide) v hb
def cl_1742 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,true),(23,false),(27,false)]
theorem inp_1742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1742 (by decide) v hb
def cl_1744 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,true),(23,false),(27,false)]
theorem inp_1744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1744 (by decide) v hb
def cl_1746 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,true),(27,false)]
theorem inp_1746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1746 (by decide) v hb
def cl_1748 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,true),(27,false)]
theorem inp_1748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1748 (by decide) v hb
def cl_1750 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,true),(27,false)]
theorem inp_1750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1750 (by decide) v hb
def cl_1752 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,true),(27,false)]
theorem inp_1752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1752 v hb
def cl_1754 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,true),(27,false)]
theorem inp_1754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1754 (by decide) v hb
def cl_1756 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,true),(23,true),(27,false)]
theorem inp_1756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1756 (by decide) v hb
end Percolation.NReplay
