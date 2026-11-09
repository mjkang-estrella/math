import NInputs026
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1758 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,true),(23,true),(27,false)]
theorem inp_1758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1758 (by decide) v hb
def cl_1760 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,true),(23,true),(27,false)]
theorem inp_1760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1760 v hb
def cl_1762 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,false),(27,true)]
theorem inp_1762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1762 (by decide) v hb
def cl_1764 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,false),(27,true)]
theorem inp_1764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1764 v hb
def cl_1766 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,false),(27,true)]
theorem inp_1766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1766 (by decide) v hb
def cl_1768 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,false),(27,true)]
theorem inp_1768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1768 v hb
def cl_1770 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,false),(27,true)]
theorem inp_1770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1770 (by decide) v hb
def cl_1772 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,true),(23,false),(27,true)]
theorem inp_1772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1772 v hb
def cl_1774 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,true),(23,false),(27,true)]
theorem inp_1774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1774 (by decide) v hb
def cl_1776 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,true),(23,false),(27,true)]
theorem inp_1776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1776 v hb
def cl_1778 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,true),(27,true)]
theorem inp_1778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1778 (by decide) v hb
def cl_1780 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,true),(27,true)]
theorem inp_1780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1780 (by decide) v hb
def cl_1782 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,true),(27,true)]
theorem inp_1782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1782 (by decide) v hb
def cl_1784 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,false),(23,true),(27,true)]
theorem inp_1784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1784 v hb
def cl_1786 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,true),(27,true)]
theorem inp_1786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) cl_1786 (by decide) v hb
def cl_1788 : CNF.NClause := [(89,false),(0,true),(7,true),(14,false),(16,true),(23,true),(27,true)]
theorem inp_1788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1788 v hb
def cl_1790 : CNF.NClause := [(89,false),(0,true),(7,false),(14,true),(16,true),(23,true),(27,true)]
theorem inp_1790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1790 v hb
def cl_1794 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,false),(28,false)]
theorem inp_1794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1794 v hb
def cl_1796 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,false),(28,false)]
theorem inp_1796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1796 v hb
def cl_1798 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,false),(28,false)]
theorem inp_1798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1798 v hb
def cl_1800 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,false),(28,false)]
theorem inp_1800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1800 v hb
def cl_1802 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,false),(28,false)]
theorem inp_1802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1802 v hb
def cl_1804 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,false),(28,false)]
theorem inp_1804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1804 v hb
def cl_1806 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,false),(28,false)]
theorem inp_1806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1806 v hb
def cl_1808 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,true),(22,false),(28,false)]
theorem inp_1808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1808 (by decide) v hb
def cl_1810 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,true),(28,false)]
theorem inp_1810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1810 (by decide) v hb
def cl_1812 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,true),(28,false)]
theorem inp_1812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1812 v hb
def cl_1814 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,true),(28,false)]
theorem inp_1814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1814 (by decide) v hb
def cl_1816 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,true),(28,false)]
theorem inp_1816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1816 (by decide) v hb
def cl_1818 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,true),(28,false)]
theorem inp_1818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1818 (by decide) v hb
def cl_1820 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,true),(28,false)]
theorem inp_1820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1820 v hb
def cl_1822 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,true),(28,false)]
theorem inp_1822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1822 (by decide) v hb
def cl_1824 : CNF.NClause := [(90,false),(0,true),(8,true),(11,true),(19,true),(22,true),(28,false)]
theorem inp_1824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1824 (by decide) v hb
def cl_1826 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,false),(28,true)]
theorem inp_1826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1826 v hb
def cl_1828 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,false),(28,true)]
theorem inp_1828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1828 v hb
def cl_1830 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,false),(28,true)]
theorem inp_1830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1830 v hb
def cl_1832 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,false),(28,true)]
theorem inp_1832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1832 v hb
def cl_1834 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,false),(28,true)]
theorem inp_1834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1834 v hb
def cl_1836 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,false),(28,true)]
theorem inp_1836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1836 v hb
def cl_1838 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,false),(28,true)]
theorem inp_1838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1838 v hb
def cl_1840 : CNF.NClause := [(90,false),(0,true),(8,true),(11,true),(19,true),(22,false),(28,true)]
theorem inp_1840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1840 (by decide) v hb
def cl_1842 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,true),(28,true)]
theorem inp_1842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1842 v hb
def cl_1844 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,true),(28,true)]
theorem inp_1844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1844 v hb
def cl_1846 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,true),(28,true)]
theorem inp_1846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1846 (by decide) v hb
def cl_1848 : CNF.NClause := [(90,false),(0,true),(8,true),(11,true),(19,false),(22,true),(28,true)]
theorem inp_1848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1848 (by decide) v hb
def cl_1850 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,true),(28,true)]
theorem inp_1850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1850 v hb
def cl_1852 : CNF.NClause := [(90,false),(0,true),(8,true),(11,false),(19,true),(22,true),(28,true)]
theorem inp_1852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1852 (by decide) v hb
def cl_1854 : CNF.NClause := [(90,false),(0,true),(8,false),(11,true),(19,true),(22,true),(28,true)]
theorem inp_1854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1854 (by decide) v hb
def cl_1858 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,false),(26,false)]
theorem inp_1858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1858 v hb
def cl_1860 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,false),(26,false)]
theorem inp_1860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1860 v hb
end Percolation.NReplay
