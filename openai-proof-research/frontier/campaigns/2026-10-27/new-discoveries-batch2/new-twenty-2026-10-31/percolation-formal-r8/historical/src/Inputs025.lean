import Inputs024
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2173 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,true),(56,true)]
theorem inp_2173 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2173 := by
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) cl_2173 (by decide) v h
def cl_2177 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,false),(54,false),(56,false)]
theorem inp_2177 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2177 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2177 (by decide) v h
def cl_2178 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,false),(56,false)]
theorem inp_2178 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2178 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2178 (by decide) v h
def cl_2179 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,false),(54,false),(56,false)]
theorem inp_2179 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2179 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2179 (by decide) v h
def cl_2180 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,false),(56,false)]
theorem inp_2180 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2180 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2180 (by decide) v h
def cl_2181 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,false),(56,false)]
theorem inp_2181 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2181 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2181 (by decide) v h
def cl_2182 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,false),(56,false)]
theorem inp_2182 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2182 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2182 (by decide) v h
def cl_2183 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,false),(54,false),(56,false)]
theorem inp_2183 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2183 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2183 (by decide) v h
def cl_2184 : CNF.NClause := [(96,true),(34,true),(39,true),(44,true),(49,false),(54,false),(56,false)]
theorem inp_2184 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2184 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2184 (by decide) v h
def cl_2189 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,false),(56,false)]
theorem inp_2189 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2189 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2189 (by decide) v h
def cl_2190 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,false),(56,false)]
theorem inp_2190 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2190 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2190 (by decide) v h
def cl_2192 : CNF.NClause := [(96,true),(34,true),(39,true),(44,true),(49,true),(54,false),(56,false)]
theorem inp_2192 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2192 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2192 (by decide) v h
def cl_2195 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,false),(54,true),(56,false)]
theorem inp_2195 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2195 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2195 (by decide) v h
def cl_2196 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,true),(56,false)]
theorem inp_2196 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2196 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2196 (by decide) v h
def cl_2197 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,true),(56,false)]
theorem inp_2197 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2197 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2197 (by decide) v h
def cl_2198 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,true),(56,false)]
theorem inp_2198 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2198 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2198 (by decide) v h
def cl_2199 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,false),(54,true),(56,false)]
theorem inp_2199 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2199 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2199 (by decide) v h
def cl_2203 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,true),(56,false)]
theorem inp_2203 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2203 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2203 (by decide) v h
def cl_2204 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,true),(54,true),(56,false)]
theorem inp_2204 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2204 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2204 (by decide) v h
def cl_2205 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,true),(56,false)]
theorem inp_2205 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2205 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2205 (by decide) v h
def cl_2206 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,true),(56,false)]
theorem inp_2206 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2206 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2206 (by decide) v h
def cl_2212 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,false),(56,true)]
theorem inp_2212 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2212 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2212 (by decide) v h
def cl_2213 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2213 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2213 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2213 (by decide) v h
def cl_2214 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2214 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2214 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2214 (by decide) v h
def cl_2215 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2215 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2215 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2215 (by decide) v h
def cl_2216 : CNF.NClause := [(96,true),(34,true),(39,true),(44,true),(49,false),(54,false),(56,true)]
theorem inp_2216 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2216 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2216 (by decide) v h
def cl_2221 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,false),(56,true)]
theorem inp_2221 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2221 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2221 (by decide) v h
def cl_2222 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,false),(56,true)]
theorem inp_2222 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2222 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2222 (by decide) v h
def cl_2228 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,true),(56,true)]
theorem inp_2228 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2228 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2228 (by decide) v h
def cl_2229 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,true),(56,true)]
theorem inp_2229 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2229 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2229 (by decide) v h
def cl_2230 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,true),(56,true)]
theorem inp_2230 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2230 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2230 (by decide) v h
def cl_2237 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,true),(56,true)]
theorem inp_2237 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2237 := by
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2237 (by decide) v h
def cl_2259 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,true),(56,false)]
theorem inp_2259 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2259 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2259 (by decide) v h
def cl_2263 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,true),(56,false)]
theorem inp_2263 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2263 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2263 (by decide) v h
def cl_2267 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,true),(56,false)]
theorem inp_2267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2267 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2267 (by decide) v h
def cl_2268 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,true),(52,true),(56,false)]
theorem inp_2268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2268 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2268 (by decide) v h
def cl_2271 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,true),(52,true),(56,false)]
theorem inp_2271 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2271 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2271 (by decide) v h
def cl_2275 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,false),(56,true)]
theorem inp_2275 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2275 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2275 (by decide) v h
def cl_2276 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,false),(52,false),(56,true)]
theorem inp_2276 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2276 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2276 (by decide) v h
def cl_2291 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,true),(56,true)]
theorem inp_2291 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2291 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2291 (by decide) v h
def cl_2299 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,true),(56,true)]
theorem inp_2299 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2299 := by
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2299 (by decide) v h
def cl_2343 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,false),(61,true)]
theorem inp_2343 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2343 := by
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2343 (by decide) v h
def cl_2359 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,true),(61,true)]
theorem inp_2359 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2359 := by
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2359 (by decide) v h
def cl_2369 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2369 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2369 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2369 (by decide) v h
def cl_2370 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2370 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2370 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2370 (by decide) v h
def cl_2371 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2371 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2371 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2371 (by decide) v h
def cl_2372 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2372 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2372 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2372 (by decide) v h
def cl_2373 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,false),(60,false)]
theorem inp_2373 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2373 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2373 (by decide) v h
def cl_2374 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,false),(60,false)]
theorem inp_2374 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2374 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2374 (by decide) v h
def cl_2377 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,false),(60,false)]
theorem inp_2377 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2377 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2377 (by decide) v h
end Percolation.Replay
