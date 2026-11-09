import Inputs022
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1889 : CNF.NClause := [(91,true),(0,false),(6,false),(12,false),(18,false),(24,false),(26,true)]
theorem inp_1889 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1889 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1889 (by decide) v h
def cl_1890 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,false),(26,true)]
theorem inp_1890 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1890 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1890 (by decide) v h
def cl_1893 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,false),(24,false),(26,true)]
theorem inp_1893 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1893 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1893 (by decide) v h
def cl_1894 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,false),(26,true)]
theorem inp_1894 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1894 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1894 (by decide) v h
def cl_1896 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,false),(26,true)]
theorem inp_1896 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1896 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1896 (by decide) v h
def cl_1897 : CNF.NClause := [(91,true),(0,false),(6,false),(12,false),(18,true),(24,false),(26,true)]
theorem inp_1897 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1897 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1897 (by decide) v h
def cl_1898 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,false),(26,true)]
theorem inp_1898 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1898 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1898 (by decide) v h
def cl_1899 : CNF.NClause := [(91,true),(0,false),(6,true),(12,false),(18,true),(24,false),(26,true)]
theorem inp_1899 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1899 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1899 (by decide) v h
def cl_1901 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,true),(24,false),(26,true)]
theorem inp_1901 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1901 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1901 (by decide) v h
def cl_1902 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,true),(24,false),(26,true)]
theorem inp_1902 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1902 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1902 (by decide) v h
def cl_1903 : CNF.NClause := [(91,true),(0,false),(6,true),(12,true),(18,true),(24,false),(26,true)]
theorem inp_1903 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1903 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1903 (by decide) v h
def cl_1904 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,false),(26,true)]
theorem inp_1904 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1904 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1904 (by decide) v h
def cl_1905 : CNF.NClause := [(91,true),(0,false),(6,false),(12,false),(18,false),(24,true),(26,true)]
theorem inp_1905 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1905 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1905 (by decide) v h
def cl_1906 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,true),(26,true)]
theorem inp_1906 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1906 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1906 (by decide) v h
def cl_1909 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,false),(24,true),(26,true)]
theorem inp_1909 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1909 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1909 (by decide) v h
def cl_1912 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,false),(24,true),(26,true)]
theorem inp_1912 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1912 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1912 (by decide) v h
def cl_1913 : CNF.NClause := [(91,true),(0,false),(6,false),(12,false),(18,true),(24,true),(26,true)]
theorem inp_1913 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1913 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1913 (by decide) v h
def cl_1914 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,true),(26,true)]
theorem inp_1914 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1914 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1914 (by decide) v h
def cl_1916 : CNF.NClause := [(91,false),(0,true),(6,true),(12,false),(18,true),(24,true),(26,true)]
theorem inp_1916 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1916 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1916 (by decide) v h
def cl_1917 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(18,true),(24,true),(26,true)]
theorem inp_1917 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1917 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1917 (by decide) v h
def cl_1918 : CNF.NClause := [(91,false),(0,true),(6,false),(12,true),(18,true),(24,true),(26,true)]
theorem inp_1918 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1918 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1918 (by decide) v h
def cl_1919 : CNF.NClause := [(91,false),(0,false),(6,true),(12,true),(18,true),(24,true),(26,true)]
theorem inp_1919 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1919 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1919 (by decide) v h
def cl_1920 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,true),(26,true)]
theorem inp_1920 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1920 := by
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) cl_1920 (by decide) v h
def cl_1921 : CNF.NClause := [(92,true),(0,false),(5,false),(10,false),(15,false),(20,false),(25,false)]
theorem inp_1921 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1921 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1921 (by decide) v h
def cl_1922 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,false),(20,false),(25,false)]
theorem inp_1922 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1922 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1922 (by decide) v h
def cl_1923 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,false),(20,false),(25,false)]
theorem inp_1923 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1923 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1923 (by decide) v h
def cl_1924 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,false),(25,false)]
theorem inp_1924 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1924 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1924 (by decide) v h
def cl_1925 : CNF.NClause := [(92,true),(0,false),(5,false),(10,true),(15,false),(20,false),(25,false)]
theorem inp_1925 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1925 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1925 (by decide) v h
def cl_1926 : CNF.NClause := [(92,true),(0,true),(5,false),(10,true),(15,false),(20,false),(25,false)]
theorem inp_1926 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1926 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1926 (by decide) v h
def cl_1927 : CNF.NClause := [(92,true),(0,false),(5,true),(10,true),(15,false),(20,false),(25,false)]
theorem inp_1927 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1927 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1927 (by decide) v h
def cl_1928 : CNF.NClause := [(92,true),(0,true),(5,true),(10,true),(15,false),(20,false),(25,false)]
theorem inp_1928 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1928 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1928 (by decide) v h
def cl_1931 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,true),(20,false),(25,false)]
theorem inp_1931 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1931 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1931 (by decide) v h
def cl_1932 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,true),(20,false),(25,false)]
theorem inp_1932 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1932 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1932 (by decide) v h
def cl_1935 : CNF.NClause := [(92,true),(0,false),(5,true),(10,true),(15,true),(20,false),(25,false)]
theorem inp_1935 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1935 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1935 (by decide) v h
def cl_1936 : CNF.NClause := [(92,true),(0,true),(5,true),(10,true),(15,true),(20,false),(25,false)]
theorem inp_1936 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1936 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1936 (by decide) v h
def cl_1939 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,false),(20,true),(25,false)]
theorem inp_1939 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1939 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1939 (by decide) v h
def cl_1940 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,true),(25,false)]
theorem inp_1940 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1940 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1940 (by decide) v h
def cl_1943 : CNF.NClause := [(92,true),(0,false),(5,true),(10,true),(15,false),(20,true),(25,false)]
theorem inp_1943 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1943 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1943 (by decide) v h
def cl_1944 : CNF.NClause := [(92,true),(0,true),(5,true),(10,true),(15,false),(20,true),(25,false)]
theorem inp_1944 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1944 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1944 (by decide) v h
def cl_1947 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,true),(20,true),(25,false)]
theorem inp_1947 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1947 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1947 (by decide) v h
def cl_1948 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,true),(20,true),(25,false)]
theorem inp_1948 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1948 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1948 (by decide) v h
def cl_1951 : CNF.NClause := [(92,true),(0,false),(5,true),(10,true),(15,true),(20,true),(25,false)]
theorem inp_1951 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1951 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1951 (by decide) v h
def cl_1952 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,true),(20,true),(25,false)]
theorem inp_1952 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1952 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1952 (by decide) v h
def cl_1953 : CNF.NClause := [(92,true),(0,false),(5,false),(10,false),(15,false),(20,false),(25,true)]
theorem inp_1953 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1953 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1953 (by decide) v h
def cl_1955 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,false),(20,false),(25,true)]
theorem inp_1955 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1955 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1955 (by decide) v h
def cl_1956 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,false),(25,true)]
theorem inp_1956 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1956 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1956 (by decide) v h
def cl_1959 : CNF.NClause := [(92,true),(0,false),(5,true),(10,true),(15,false),(20,false),(25,true)]
theorem inp_1959 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1959 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1959 (by decide) v h
def cl_1960 : CNF.NClause := [(92,true),(0,true),(5,true),(10,true),(15,false),(20,false),(25,true)]
theorem inp_1960 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1960 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1960 (by decide) v h
def cl_1963 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,true),(20,false),(25,true)]
theorem inp_1963 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1963 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1963 (by decide) v h
def cl_1964 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,true),(20,false),(25,true)]
theorem inp_1964 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1964 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1964 (by decide) v h
end Percolation.Replay
