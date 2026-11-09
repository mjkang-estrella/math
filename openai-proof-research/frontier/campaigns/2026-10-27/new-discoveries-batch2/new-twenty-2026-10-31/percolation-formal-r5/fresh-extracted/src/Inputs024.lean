import Inputs023
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1967 : CNF.NClause := [(92,true),(0,false),(5,true),(10,true),(15,true),(20,false),(25,true)]
theorem inp_1967 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1967 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1967 (by decide) v h
def cl_1968 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,true),(20,false),(25,true)]
theorem inp_1968 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1968 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1968 (by decide) v h
def cl_1971 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,false),(20,true),(25,true)]
theorem inp_1971 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1971 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1971 (by decide) v h
def cl_1972 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,true),(25,true)]
theorem inp_1972 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1972 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1972 (by decide) v h
def cl_1975 : CNF.NClause := [(92,true),(0,false),(5,true),(10,true),(15,false),(20,true),(25,true)]
theorem inp_1975 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1975 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1975 (by decide) v h
def cl_1976 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,false),(20,true),(25,true)]
theorem inp_1976 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1976 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1976 (by decide) v h
def cl_1979 : CNF.NClause := [(92,true),(0,false),(5,true),(10,false),(15,true),(20,true),(25,true)]
theorem inp_1979 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1979 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1979 (by decide) v h
def cl_1980 : CNF.NClause := [(92,false),(0,true),(5,true),(10,false),(15,true),(20,true),(25,true)]
theorem inp_1980 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1980 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1980 (by decide) v h
def cl_1982 : CNF.NClause := [(92,false),(0,true),(5,false),(10,true),(15,true),(20,true),(25,true)]
theorem inp_1982 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1982 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1982 (by decide) v h
def cl_1983 : CNF.NClause := [(92,false),(0,false),(5,true),(10,true),(15,true),(20,true),(25,true)]
theorem inp_1983 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1983 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1983 (by decide) v h
def cl_1984 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,true),(20,true),(25,true)]
theorem inp_1984 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1984 := by
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) cl_1984 (by decide) v h
def cl_2027 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,true),(60,false),(61,true)]
theorem inp_2027 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2027 := by
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2027 (by decide) v h
def cl_2029 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,false),(61,true)]
theorem inp_2029 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2029 := by
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2029 (by decide) v h
def cl_2031 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,true),(60,false),(61,true)]
theorem inp_2031 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2031 := by
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2031 (by decide) v h
def cl_2045 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,true),(61,true)]
theorem inp_2045 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2045 := by
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2045 (by decide) v h
def cl_2049 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,false),(56,false)]
theorem inp_2049 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2049 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2049 (by decide) v h
def cl_2050 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,false),(56,false)]
theorem inp_2050 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2050 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2050 (by decide) v h
def cl_2059 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,false),(56,false)]
theorem inp_2059 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2059 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2059 (by decide) v h
def cl_2060 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,true),(55,false),(56,false)]
theorem inp_2060 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2060 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2060 (by decide) v h
def cl_2063 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,false),(56,false)]
theorem inp_2063 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2063 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2063 (by decide) v h
def cl_2064 : CNF.NClause := [(94,true),(35,true),(40,true),(45,true),(50,true),(55,false),(56,false)]
theorem inp_2064 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2064 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2064 (by decide) v h
def cl_2075 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,true),(56,false)]
theorem inp_2075 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2075 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2075 (by decide) v h
def cl_2079 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,true),(56,false)]
theorem inp_2079 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2079 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2079 (by decide) v h
def cl_2091 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,false),(56,true)]
theorem inp_2091 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2091 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2091 (by decide) v h
def cl_2092 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,true),(55,false),(56,true)]
theorem inp_2092 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2092 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2092 (by decide) v h
def cl_2095 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,false),(56,true)]
theorem inp_2095 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2095 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2095 (by decide) v h
def cl_2107 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,true),(56,true)]
theorem inp_2107 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2107 := by
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2107 (by decide) v h
def cl_2113 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2113 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2113 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2113 (by decide) v h
def cl_2114 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2114 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2114 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2114 (by decide) v h
def cl_2115 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2115 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2115 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2115 (by decide) v h
def cl_2116 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2116 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2116 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2116 (by decide) v h
def cl_2119 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,false),(56,false)]
theorem inp_2119 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2119 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2119 (by decide) v h
def cl_2120 : CNF.NClause := [(95,true),(33,true),(38,true),(43,true),(48,false),(53,false),(56,false)]
theorem inp_2120 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2120 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2120 (by decide) v h
def cl_2123 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,false),(56,false)]
theorem inp_2123 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2123 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2123 (by decide) v h
def cl_2124 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,false),(56,false)]
theorem inp_2124 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2124 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2124 (by decide) v h
def cl_2125 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,false),(56,false)]
theorem inp_2125 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2125 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2125 (by decide) v h
def cl_2127 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,true),(53,false),(56,false)]
theorem inp_2127 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2127 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2127 (by decide) v h
def cl_2131 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,true),(56,false)]
theorem inp_2131 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2131 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2131 (by decide) v h
def cl_2132 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,true),(56,false)]
theorem inp_2132 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2132 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2132 (by decide) v h
def cl_2135 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,true),(56,false)]
theorem inp_2135 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2135 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2135 (by decide) v h
def cl_2136 : CNF.NClause := [(95,true),(33,true),(38,true),(43,true),(48,false),(53,true),(56,false)]
theorem inp_2136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2136 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2136 (by decide) v h
def cl_2139 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,true),(56,false)]
theorem inp_2139 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2139 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2139 (by decide) v h
def cl_2140 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,true),(56,false)]
theorem inp_2140 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2140 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2140 (by decide) v h
def cl_2141 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,true),(56,false)]
theorem inp_2141 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2141 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2141 (by decide) v h
def cl_2143 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,true),(53,true),(56,false)]
theorem inp_2143 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2143 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2143 (by decide) v h
def cl_2151 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,false),(56,true)]
theorem inp_2151 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2151 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2151 (by decide) v h
def cl_2157 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,false),(56,true)]
theorem inp_2157 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2157 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2157 (by decide) v h
def cl_2159 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,true),(53,false),(56,true)]
theorem inp_2159 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2159 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2159 (by decide) v h
def cl_2163 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,true),(56,true)]
theorem inp_2163 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2163 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2163 (by decide) v h
def cl_2167 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,true),(56,true)]
theorem inp_2167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2167 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2167 (by decide) v h
end Percolation.Replay
