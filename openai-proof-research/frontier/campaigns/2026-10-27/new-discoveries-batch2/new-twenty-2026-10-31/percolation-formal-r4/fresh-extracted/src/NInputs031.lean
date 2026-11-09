import NInputs030
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2109 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,true),(56,true)]
theorem inp_2109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2109 (by decide) v hb
def cl_2110 : CNF.NClause := [(94,false),(35,true),(40,false),(45,true),(50,true),(55,true),(56,true)]
theorem inp_2110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2110 (by decide) v hb
def cl_2111 : CNF.NClause := [(94,false),(35,false),(40,true),(45,true),(50,true),(55,true),(56,true)]
theorem inp_2111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2111 (by decide) v hb
def cl_2112 : CNF.NClause := [(94,false),(35,true),(40,true),(45,true),(50,true),(55,true),(56,true)]
theorem inp_2112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2112 (by decide) v hb
def cl_2113 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2113 v hb
def cl_2114 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2114 v hb
def cl_2115 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2115 v hb
def cl_2116 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,false),(56,false)]
theorem inp_2116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2116 v hb
def cl_2117 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,false),(56,false)]
theorem inp_2117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2117 (by decide) v hb
def cl_2118 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,false),(56,false)]
theorem inp_2118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2118 (by decide) v hb
def cl_2119 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,false),(56,false)]
theorem inp_2119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2119 v hb
def cl_2121 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,false),(56,false)]
theorem inp_2121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2121 (by decide) v hb
def cl_2122 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,true),(53,false),(56,false)]
theorem inp_2122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2122 (by decide) v hb
def cl_2123 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,false),(56,false)]
theorem inp_2123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2123 v hb
def cl_2124 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,false),(56,false)]
theorem inp_2124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2124 v hb
def cl_2125 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,false),(56,false)]
theorem inp_2125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2125 v hb
def cl_2126 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,true),(53,false),(56,false)]
theorem inp_2126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2126 (by decide) v hb
def cl_2127 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,true),(53,false),(56,false)]
theorem inp_2127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2127 v hb
def cl_2129 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,true),(56,false)]
theorem inp_2129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2129 (by decide) v hb
def cl_2130 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,true),(56,false)]
theorem inp_2130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2130 (by decide) v hb
def cl_2131 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,true),(56,false)]
theorem inp_2131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2131 v hb
def cl_2132 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,true),(56,false)]
theorem inp_2132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2132 v hb
def cl_2133 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,true),(56,false)]
theorem inp_2133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2133 (by decide) v hb
def cl_2134 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,true),(56,false)]
theorem inp_2134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2134 (by decide) v hb
def cl_2137 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,true),(56,false)]
theorem inp_2137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2137 (by decide) v hb
def cl_2139 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,true),(56,false)]
theorem inp_2139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2139 v hb
def cl_2140 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,true),(56,false)]
theorem inp_2140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2140 v hb
def cl_2141 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,true),(56,false)]
theorem inp_2141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2141 v hb
def cl_2145 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,false),(56,true)]
theorem inp_2145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2145 (by decide) v hb
def cl_2146 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,false),(56,true)]
theorem inp_2146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2146 (by decide) v hb
def cl_2147 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,false),(56,true)]
theorem inp_2147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2147 (by decide) v hb
def cl_2148 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,false),(56,true)]
theorem inp_2148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2148 (by decide) v hb
def cl_2149 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,false),(56,true)]
theorem inp_2149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2149 (by decide) v hb
def cl_2150 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,false),(56,true)]
theorem inp_2150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2150 (by decide) v hb
def cl_2151 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,false),(56,true)]
theorem inp_2151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2151 v hb
def cl_2152 : CNF.NClause := [(95,true),(33,true),(38,true),(43,true),(48,false),(53,false),(56,true)]
theorem inp_2152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2152 (by decide) v hb
def cl_2153 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,false),(56,true)]
theorem inp_2153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2153 (by decide) v hb
def cl_2154 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,true),(53,false),(56,true)]
theorem inp_2154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2154 (by decide) v hb
def cl_2155 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,false),(56,true)]
theorem inp_2155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2155 (by decide) v hb
def cl_2156 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,false),(56,true)]
theorem inp_2156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2156 (by decide) v hb
def cl_2157 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,false),(56,true)]
theorem inp_2157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2157 v hb
def cl_2158 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,true),(53,false),(56,true)]
theorem inp_2158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2158 (by decide) v hb
def cl_2159 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,true),(53,false),(56,true)]
theorem inp_2159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2159 v hb
def cl_2160 : CNF.NClause := [(95,false),(33,true),(38,true),(43,true),(48,true),(53,false),(56,true)]
theorem inp_2160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2160 (by decide) v hb
def cl_2161 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,true),(56,true)]
theorem inp_2161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2161 (by decide) v hb
def cl_2162 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,true),(56,true)]
theorem inp_2162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2162 (by decide) v hb
def cl_2163 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,true),(56,true)]
theorem inp_2163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2163 v hb
def cl_2164 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,true),(56,true)]
theorem inp_2164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2164 (by decide) v hb
def cl_2165 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,true),(56,true)]
theorem inp_2165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2165 (by decide) v hb
def cl_2166 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,true),(56,true)]
theorem inp_2166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2166 (by decide) v hb
end Percolation.NReplay
