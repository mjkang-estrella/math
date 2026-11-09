import NInputs029
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2052 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,false),(55,false),(56,false)]
theorem inp_2052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2052 (by decide) v hb
def cl_2053 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,false),(56,false)]
theorem inp_2053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2053 (by decide) v hb
def cl_2054 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,false),(56,false)]
theorem inp_2054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2054 (by decide) v hb
def cl_2055 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,false),(56,false)]
theorem inp_2055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2055 (by decide) v hb
def cl_2056 : CNF.NClause := [(94,true),(35,true),(40,true),(45,true),(50,false),(55,false),(56,false)]
theorem inp_2056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2056 (by decide) v hb
def cl_2057 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,true),(55,false),(56,false)]
theorem inp_2057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2057 (by decide) v hb
def cl_2058 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,false),(56,false)]
theorem inp_2058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2058 (by decide) v hb
def cl_2059 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,false),(56,false)]
theorem inp_2059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2059 v hb
def cl_2060 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,true),(55,false),(56,false)]
theorem inp_2060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2060 v hb
def cl_2061 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,false),(56,false)]
theorem inp_2061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2061 (by decide) v hb
def cl_2062 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,true),(55,false),(56,false)]
theorem inp_2062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2062 (by decide) v hb
def cl_2063 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,false),(56,false)]
theorem inp_2063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2063 v hb
def cl_2065 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,true),(56,false)]
theorem inp_2065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2065 (by decide) v hb
def cl_2066 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,true),(56,false)]
theorem inp_2066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2066 (by decide) v hb
def cl_2067 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,true),(56,false)]
theorem inp_2067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2067 (by decide) v hb
def cl_2069 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,true),(56,false)]
theorem inp_2069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2069 (by decide) v hb
def cl_2070 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,true),(56,false)]
theorem inp_2070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2070 (by decide) v hb
def cl_2071 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,true),(56,false)]
theorem inp_2071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2071 (by decide) v hb
def cl_2074 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,true),(56,false)]
theorem inp_2074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2074 (by decide) v hb
def cl_2075 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,true),(56,false)]
theorem inp_2075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2075 v hb
def cl_2077 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,true),(56,false)]
theorem inp_2077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2077 (by decide) v hb
def cl_2079 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,true),(56,false)]
theorem inp_2079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2079 v hb
def cl_2081 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,false),(56,true)]
theorem inp_2081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2081 (by decide) v hb
def cl_2082 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,false),(56,true)]
theorem inp_2082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2082 (by decide) v hb
def cl_2083 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,false),(56,true)]
theorem inp_2083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2083 (by decide) v hb
def cl_2084 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,false),(55,false),(56,true)]
theorem inp_2084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2084 (by decide) v hb
def cl_2085 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,false),(56,true)]
theorem inp_2085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2085 (by decide) v hb
def cl_2086 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,false),(56,true)]
theorem inp_2086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2086 (by decide) v hb
def cl_2087 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,false),(56,true)]
theorem inp_2087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2087 (by decide) v hb
def cl_2088 : CNF.NClause := [(94,true),(35,true),(40,true),(45,true),(50,false),(55,false),(56,true)]
theorem inp_2088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2088 (by decide) v hb
def cl_2089 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,true),(55,false),(56,true)]
theorem inp_2089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2089 (by decide) v hb
def cl_2090 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,false),(56,true)]
theorem inp_2090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2090 (by decide) v hb
def cl_2091 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,false),(56,true)]
theorem inp_2091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2091 v hb
def cl_2092 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,true),(55,false),(56,true)]
theorem inp_2092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2092 v hb
def cl_2093 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,false),(56,true)]
theorem inp_2093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2093 (by decide) v hb
def cl_2094 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,true),(55,false),(56,true)]
theorem inp_2094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2094 (by decide) v hb
def cl_2095 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,false),(56,true)]
theorem inp_2095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2095 v hb
def cl_2096 : CNF.NClause := [(94,false),(35,true),(40,true),(45,true),(50,true),(55,false),(56,true)]
theorem inp_2096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2096 (by decide) v hb
def cl_2097 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,true),(56,true)]
theorem inp_2097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2097 (by decide) v hb
def cl_2098 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,true),(56,true)]
theorem inp_2098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2098 (by decide) v hb
def cl_2099 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,true),(56,true)]
theorem inp_2099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2099 (by decide) v hb
def cl_2100 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,false),(55,true),(56,true)]
theorem inp_2100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2100 (by decide) v hb
def cl_2101 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,true),(56,true)]
theorem inp_2101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2101 (by decide) v hb
def cl_2102 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,true),(56,true)]
theorem inp_2102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2102 (by decide) v hb
def cl_2103 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,true),(56,true)]
theorem inp_2103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2103 (by decide) v hb
def cl_2104 : CNF.NClause := [(94,false),(35,true),(40,true),(45,true),(50,false),(55,true),(56,true)]
theorem inp_2104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2104 (by decide) v hb
def cl_2105 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,true),(55,true),(56,true)]
theorem inp_2105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2105 (by decide) v hb
def cl_2106 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,true),(56,true)]
theorem inp_2106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2106 (by decide) v hb
def cl_2107 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,true),(56,true)]
theorem inp_2107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2107 v hb
def cl_2108 : CNF.NClause := [(94,false),(35,true),(40,true),(45,false),(50,true),(55,true),(56,true)]
theorem inp_2108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2108 (by decide) v hb
end Percolation.NReplay
