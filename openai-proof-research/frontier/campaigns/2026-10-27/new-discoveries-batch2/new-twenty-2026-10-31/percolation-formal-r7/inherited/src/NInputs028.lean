import NInputs027
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1862 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,false),(26,false)]
theorem inp_1862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1862 v hb
def cl_1864 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,false),(26,false)]
theorem inp_1864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1864 v hb
def cl_1866 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,false),(26,false)]
theorem inp_1866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1866 (by decide) v hb
def cl_1868 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,false),(26,false)]
theorem inp_1868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1868 v hb
def cl_1870 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,true),(24,false),(26,false)]
theorem inp_1870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1870 (by decide) v hb
def cl_1872 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,true),(24,false),(26,false)]
theorem inp_1872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1872 v hb
def cl_1874 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,true),(26,false)]
theorem inp_1874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1874 v hb
def cl_1876 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,true),(26,false)]
theorem inp_1876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1876 v hb
def cl_1878 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,true),(26,false)]
theorem inp_1878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1878 (by decide) v hb
def cl_1880 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,true),(26,false)]
theorem inp_1880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1880 v hb
def cl_1882 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,true),(26,false)]
theorem inp_1882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1882 (by decide) v hb
def cl_1884 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,true),(26,false)]
theorem inp_1884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1884 v hb
def cl_1886 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,true),(24,true),(26,false)]
theorem inp_1886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1886 (by decide) v hb
def cl_1888 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,true),(26,false)]
theorem inp_1888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1888 v hb
def cl_1890 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,false),(26,true)]
theorem inp_1890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1890 v hb
def cl_1892 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,false),(26,true)]
theorem inp_1892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1892 (by decide) v hb
def cl_1894 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,false),(26,true)]
theorem inp_1894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1894 v hb
def cl_1896 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,false),(26,true)]
theorem inp_1896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1896 v hb
def cl_1898 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,false),(26,true)]
theorem inp_1898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1898 v hb
def cl_1900 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,false),(26,true)]
theorem inp_1900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1900 (by decide) v hb
def cl_1902 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,true),(24,false),(26,true)]
theorem inp_1902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1902 v hb
def cl_1904 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,false),(26,true)]
theorem inp_1904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1904 v hb
def cl_1906 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,true),(26,true)]
theorem inp_1906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1906 v hb
def cl_1908 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,true),(26,true)]
theorem inp_1908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1908 (by decide) v hb
def cl_1910 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,true),(26,true)]
theorem inp_1910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1910 (by decide) v hb
def cl_1912 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,false),(24,true),(26,true)]
theorem inp_1912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1912 v hb
def cl_1914 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,true),(26,true)]
theorem inp_1914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1914 v hb
def cl_1916 : CNF.NClause := [(91,false),(0,true),(6,true),(12,false),(18,true),(24,true),(26,true)]
theorem inp_1916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1916 v hb
def cl_1918 : CNF.NClause := [(91,false),(0,true),(6,false),(12,true),(18,true),(24,true),(26,true)]
theorem inp_1918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1918 v hb
def cl_1920 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,true),(26,true)]
theorem inp_1920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1920 v hb
def cl_1954 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,false),(20,false),(25,true)]
theorem inp_1954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1954 (by decide) v hb
def cl_1956 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,false),(25,true)]
theorem inp_1956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1956 v hb
def cl_1958 : CNF.NClause := [(92,true),(0,true),(5,false),(10,true),(15,false),(20,false),(25,true)]
theorem inp_1958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1958 (by decide) v hb
def cl_1960 : CNF.NClause := [(92,true),(0,true),(5,true),(10,true),(15,false),(20,false),(25,true)]
theorem inp_1960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1960 v hb
def cl_1962 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,true),(20,false),(25,true)]
theorem inp_1962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1962 (by decide) v hb
def cl_1964 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,true),(20,false),(25,true)]
theorem inp_1964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1964 v hb
def cl_1966 : CNF.NClause := [(92,true),(0,true),(5,false),(10,true),(15,true),(20,false),(25,true)]
theorem inp_1966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1966 (by decide) v hb
def cl_1968 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,true),(20,false),(25,true)]
theorem inp_1968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1968 v hb
def cl_1970 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,false),(20,true),(25,true)]
theorem inp_1970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1970 (by decide) v hb
def cl_1972 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,true),(25,true)]
theorem inp_1972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1972 v hb
def cl_1974 : CNF.NClause := [(92,true),(0,true),(5,false),(10,true),(15,false),(20,true),(25,true)]
theorem inp_1974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1974 (by decide) v hb
def cl_1976 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,false),(20,true),(25,true)]
theorem inp_1976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1976 v hb
def cl_1978 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,true),(20,true),(25,true)]
theorem inp_1978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1978 (by decide) v hb
def cl_1980 : CNF.NClause := [(92,false),(0,true),(5,true),(10,false),(15,true),(20,true),(25,true)]
theorem inp_1980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1980 v hb
def cl_1982 : CNF.NClause := [(92,false),(0,true),(5,false),(10,true),(15,true),(20,true),(25,true)]
theorem inp_1982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1982 v hb
def cl_1985 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,false),(61,false)]
theorem inp_1985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1985 (by decide) v hb
def cl_1986 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,false),(61,false)]
theorem inp_1986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1986 (by decide) v hb
def cl_1987 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,false),(60,false),(61,false)]
theorem inp_1987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1987 (by decide) v hb
def cl_1988 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,false),(61,false)]
theorem inp_1988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1988 (by decide) v hb
def cl_1989 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,false),(61,false)]
theorem inp_1989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1989 (by decide) v hb
end Percolation.NReplay
