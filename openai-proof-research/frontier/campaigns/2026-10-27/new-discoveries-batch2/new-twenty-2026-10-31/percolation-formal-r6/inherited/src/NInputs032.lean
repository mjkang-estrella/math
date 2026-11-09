import NInputs031
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2167 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,true),(56,true)]
theorem inp_2167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2167 v hb
def cl_2168 : CNF.NClause := [(95,false),(33,true),(38,true),(43,true),(48,false),(53,true),(56,true)]
theorem inp_2168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2168 (by decide) v hb
def cl_2169 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,true),(56,true)]
theorem inp_2169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2169 (by decide) v hb
def cl_2170 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,true),(53,true),(56,true)]
theorem inp_2170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2170 (by decide) v hb
def cl_2171 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,true),(56,true)]
theorem inp_2171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2171 (by decide) v hb
def cl_2172 : CNF.NClause := [(95,false),(33,true),(38,true),(43,false),(48,true),(53,true),(56,true)]
theorem inp_2172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2172 (by decide) v hb
def cl_2173 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,true),(56,true)]
theorem inp_2173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2173 v hb
def cl_2174 : CNF.NClause := [(95,false),(33,true),(38,false),(43,true),(48,true),(53,true),(56,true)]
theorem inp_2174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2174 (by decide) v hb
def cl_2175 : CNF.NClause := [(95,false),(33,false),(38,true),(43,true),(48,true),(53,true),(56,true)]
theorem inp_2175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2175 (by decide) v hb
def cl_2176 : CNF.NClause := [(95,false),(33,true),(38,true),(43,true),(48,true),(53,true),(56,true)]
theorem inp_2176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2176 (by decide) v hb
def cl_2178 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,false),(56,false)]
theorem inp_2178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2178 v hb
def cl_2180 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,false),(56,false)]
theorem inp_2180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2180 v hb
def cl_2182 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,false),(56,false)]
theorem inp_2182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2182 v hb
def cl_2184 : CNF.NClause := [(96,true),(34,true),(39,true),(44,true),(49,false),(54,false),(56,false)]
theorem inp_2184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2184 v hb
def cl_2185 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,false),(56,false)]
theorem inp_2185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2185 (by decide) v hb
def cl_2186 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,false),(56,false)]
theorem inp_2186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2186 (by decide) v hb
def cl_2188 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,true),(54,false),(56,false)]
theorem inp_2188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2188 (by decide) v hb
def cl_2190 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,false),(56,false)]
theorem inp_2190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2190 v hb
def cl_2193 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,false),(54,true),(56,false)]
theorem inp_2193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2193 (by decide) v hb
def cl_2194 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,true),(56,false)]
theorem inp_2194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2194 (by decide) v hb
def cl_2197 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,true),(56,false)]
theorem inp_2197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2197 v hb
def cl_2198 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,true),(56,false)]
theorem inp_2198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2198 v hb
def cl_2201 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,true),(56,false)]
theorem inp_2201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2201 (by decide) v hb
def cl_2202 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,true),(56,false)]
theorem inp_2202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2202 (by decide) v hb
def cl_2203 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,true),(56,false)]
theorem inp_2203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2203 v hb
def cl_2204 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,true),(54,true),(56,false)]
theorem inp_2204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2204 v hb
def cl_2205 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,true),(56,false)]
theorem inp_2205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2205 v hb
def cl_2206 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,true),(56,false)]
theorem inp_2206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2206 v hb
def cl_2209 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,false),(54,false),(56,true)]
theorem inp_2209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2209 (by decide) v hb
def cl_2210 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,false),(56,true)]
theorem inp_2210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2210 (by decide) v hb
def cl_2211 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,false),(54,false),(56,true)]
theorem inp_2211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2211 (by decide) v hb
def cl_2212 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,false),(56,true)]
theorem inp_2212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2212 v hb
def cl_2213 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2213 v hb
def cl_2214 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2214 v hb
def cl_2215 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2215 v hb
def cl_2216 : CNF.NClause := [(96,true),(34,true),(39,true),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2216 v hb
def cl_2217 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,false),(56,true)]
theorem inp_2217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2217 (by decide) v hb
def cl_2218 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,false),(56,true)]
theorem inp_2218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2218 (by decide) v hb
def cl_2219 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,false),(56,true)]
theorem inp_2219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2219 (by decide) v hb
def cl_2220 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,true),(54,false),(56,true)]
theorem inp_2220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2220 (by decide) v hb
def cl_2221 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,false),(56,true)]
theorem inp_2221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2221 v hb
def cl_2222 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,false),(56,true)]
theorem inp_2222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2222 v hb
def cl_2223 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,true),(54,false),(56,true)]
theorem inp_2223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2223 (by decide) v hb
def cl_2224 : CNF.NClause := [(96,false),(34,true),(39,true),(44,true),(49,true),(54,false),(56,true)]
theorem inp_2224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2224 (by decide) v hb
def cl_2225 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,false),(54,true),(56,true)]
theorem inp_2225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2225 (by decide) v hb
def cl_2226 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,true),(56,true)]
theorem inp_2226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2226 (by decide) v hb
def cl_2227 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,false),(54,true),(56,true)]
theorem inp_2227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2227 (by decide) v hb
def cl_2228 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,true),(56,true)]
theorem inp_2228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2228 v hb
def cl_2229 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,true),(56,true)]
theorem inp_2229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2229 v hb
def cl_2230 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,true),(56,true)]
theorem inp_2230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2230 v hb
end Percolation.NReplay
