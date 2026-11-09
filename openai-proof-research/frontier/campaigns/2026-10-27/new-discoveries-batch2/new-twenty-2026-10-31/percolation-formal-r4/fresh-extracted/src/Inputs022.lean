import Inputs021
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1817 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(19,true),(22,true),(28,false)]
theorem inp_1817 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1817 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1817 (by decide) v h
def cl_1819 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,true),(22,true),(28,false)]
theorem inp_1819 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1819 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1819 (by decide) v h
def cl_1820 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,true),(28,false)]
theorem inp_1820 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1820 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1820 (by decide) v h
def cl_1823 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,true),(22,true),(28,false)]
theorem inp_1823 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1823 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1823 (by decide) v h
def cl_1825 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(19,false),(22,false),(28,true)]
theorem inp_1825 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1825 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1825 (by decide) v h
def cl_1826 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,false),(28,true)]
theorem inp_1826 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1826 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1826 (by decide) v h
def cl_1827 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,false),(22,false),(28,true)]
theorem inp_1827 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1827 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1827 (by decide) v h
def cl_1828 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,false),(28,true)]
theorem inp_1828 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1828 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1828 (by decide) v h
def cl_1829 : CNF.NClause := [(90,true),(0,false),(8,false),(11,true),(19,false),(22,false),(28,true)]
theorem inp_1829 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1829 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1829 (by decide) v h
def cl_1830 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,false),(28,true)]
theorem inp_1830 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1830 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1830 (by decide) v h
def cl_1831 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,false),(22,false),(28,true)]
theorem inp_1831 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1831 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1831 (by decide) v h
def cl_1832 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,false),(28,true)]
theorem inp_1832 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1832 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1832 (by decide) v h
def cl_1833 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(19,true),(22,false),(28,true)]
theorem inp_1833 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1833 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1833 (by decide) v h
def cl_1834 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,false),(28,true)]
theorem inp_1834 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1834 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1834 (by decide) v h
def cl_1835 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,true),(22,false),(28,true)]
theorem inp_1835 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1835 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1835 (by decide) v h
def cl_1836 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,false),(28,true)]
theorem inp_1836 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1836 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1836 (by decide) v h
def cl_1837 : CNF.NClause := [(90,true),(0,false),(8,false),(11,true),(19,true),(22,false),(28,true)]
theorem inp_1837 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1837 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1837 (by decide) v h
def cl_1838 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,false),(28,true)]
theorem inp_1838 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1838 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1838 (by decide) v h
def cl_1839 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,true),(22,false),(28,true)]
theorem inp_1839 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1839 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1839 (by decide) v h
def cl_1841 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(19,false),(22,true),(28,true)]
theorem inp_1841 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1841 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1841 (by decide) v h
def cl_1842 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,true),(28,true)]
theorem inp_1842 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1842 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1842 (by decide) v h
def cl_1843 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,false),(22,true),(28,true)]
theorem inp_1843 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1843 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1843 (by decide) v h
def cl_1844 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,true),(28,true)]
theorem inp_1844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1844 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1844 (by decide) v h
def cl_1847 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,false),(22,true),(28,true)]
theorem inp_1847 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1847 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1847 (by decide) v h
def cl_1849 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(19,true),(22,true),(28,true)]
theorem inp_1849 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1849 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1849 (by decide) v h
def cl_1850 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,true),(28,true)]
theorem inp_1850 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1850 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1850 (by decide) v h
def cl_1851 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,true),(22,true),(28,true)]
theorem inp_1851 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1851 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1851 (by decide) v h
def cl_1853 : CNF.NClause := [(90,true),(0,false),(8,false),(11,true),(19,true),(22,true),(28,true)]
theorem inp_1853 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1853 := by
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) cl_1853 (by decide) v h
def cl_1857 : CNF.NClause := [(91,true),(0,false),(6,false),(12,false),(18,false),(24,false),(26,false)]
theorem inp_1857 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1857 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1857 (by decide) v h
def cl_1858 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,false),(26,false)]
theorem inp_1858 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1858 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1858 (by decide) v h
def cl_1859 : CNF.NClause := [(91,true),(0,false),(6,true),(12,false),(18,false),(24,false),(26,false)]
theorem inp_1859 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1859 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1859 (by decide) v h
def cl_1860 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,false),(26,false)]
theorem inp_1860 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1860 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1860 (by decide) v h
def cl_1861 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,false),(24,false),(26,false)]
theorem inp_1861 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1861 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1861 (by decide) v h
def cl_1862 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,false),(26,false)]
theorem inp_1862 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1862 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1862 (by decide) v h
def cl_1863 : CNF.NClause := [(91,true),(0,false),(6,true),(12,true),(18,false),(24,false),(26,false)]
theorem inp_1863 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1863 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1863 (by decide) v h
def cl_1864 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,false),(26,false)]
theorem inp_1864 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1864 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1864 (by decide) v h
def cl_1867 : CNF.NClause := [(91,true),(0,false),(6,true),(12,false),(18,true),(24,false),(26,false)]
theorem inp_1867 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1867 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1867 (by decide) v h
def cl_1868 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,false),(26,false)]
theorem inp_1868 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1868 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1868 (by decide) v h
def cl_1869 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,true),(24,false),(26,false)]
theorem inp_1869 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1869 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1869 (by decide) v h
def cl_1871 : CNF.NClause := [(91,true),(0,false),(6,true),(12,true),(18,true),(24,false),(26,false)]
theorem inp_1871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1871 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1871 (by decide) v h
def cl_1872 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,true),(24,false),(26,false)]
theorem inp_1872 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1872 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1872 (by decide) v h
def cl_1873 : CNF.NClause := [(91,true),(0,false),(6,false),(12,false),(18,false),(24,true),(26,false)]
theorem inp_1873 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1873 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1873 (by decide) v h
def cl_1874 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,true),(26,false)]
theorem inp_1874 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1874 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1874 (by decide) v h
def cl_1875 : CNF.NClause := [(91,true),(0,false),(6,true),(12,false),(18,false),(24,true),(26,false)]
theorem inp_1875 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1875 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1875 (by decide) v h
def cl_1876 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,true),(26,false)]
theorem inp_1876 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1876 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1876 (by decide) v h
def cl_1877 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,false),(24,true),(26,false)]
theorem inp_1877 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1877 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1877 (by decide) v h
def cl_1880 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,true),(26,false)]
theorem inp_1880 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1880 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1880 (by decide) v h
def cl_1884 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,true),(26,false)]
theorem inp_1884 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1884 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1884 (by decide) v h
def cl_1885 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,true),(24,true),(26,false)]
theorem inp_1885 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1885 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1885 (by decide) v h
def cl_1888 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,true),(26,false)]
theorem inp_1888 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1888 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1888 (by decide) v h
end Percolation.Replay
