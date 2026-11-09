import NInputs032
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2231 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,false),(54,true),(56,true)]
theorem inp_2231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2231 (by decide) v hb
def cl_2232 : CNF.NClause := [(96,false),(34,true),(39,true),(44,true),(49,false),(54,true),(56,true)]
theorem inp_2232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2232 (by decide) v hb
def cl_2233 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,true),(56,true)]
theorem inp_2233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2233 (by decide) v hb
def cl_2234 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,true),(56,true)]
theorem inp_2234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2234 (by decide) v hb
def cl_2235 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,true),(56,true)]
theorem inp_2235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2235 (by decide) v hb
def cl_2236 : CNF.NClause := [(96,false),(34,true),(39,true),(44,false),(49,true),(54,true),(56,true)]
theorem inp_2236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2236 (by decide) v hb
def cl_2237 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,true),(56,true)]
theorem inp_2237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2237 v hb
def cl_2238 : CNF.NClause := [(96,false),(34,true),(39,false),(44,true),(49,true),(54,true),(56,true)]
theorem inp_2238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2238 (by decide) v hb
def cl_2239 : CNF.NClause := [(96,false),(34,false),(39,true),(44,true),(49,true),(54,true),(56,true)]
theorem inp_2239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2239 (by decide) v hb
def cl_2240 : CNF.NClause := [(96,false),(34,true),(39,true),(44,true),(49,true),(54,true),(56,true)]
theorem inp_2240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) cl_2240 (by decide) v hb
def cl_2241 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,false),(56,false)]
theorem inp_2241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2241 (by decide) v hb
def cl_2242 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,false),(56,false)]
theorem inp_2242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2242 (by decide) v hb
def cl_2243 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,false),(56,false)]
theorem inp_2243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2243 (by decide) v hb
def cl_2244 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,false),(52,false),(56,false)]
theorem inp_2244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2244 (by decide) v hb
def cl_2245 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,false),(56,false)]
theorem inp_2245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2245 (by decide) v hb
def cl_2246 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,false),(56,false)]
theorem inp_2246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2246 (by decide) v hb
def cl_2247 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,false),(56,false)]
theorem inp_2247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2247 (by decide) v hb
def cl_2248 : CNF.NClause := [(97,true),(32,true),(37,true),(42,true),(47,false),(52,false),(56,false)]
theorem inp_2248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2248 (by decide) v hb
def cl_2249 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,true),(52,false),(56,false)]
theorem inp_2249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2249 (by decide) v hb
def cl_2250 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,false),(56,false)]
theorem inp_2250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2250 (by decide) v hb
def cl_2251 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,false),(56,false)]
theorem inp_2251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2251 (by decide) v hb
def cl_2252 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,true),(52,false),(56,false)]
theorem inp_2252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2252 (by decide) v hb
def cl_2253 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,true),(52,false),(56,false)]
theorem inp_2253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2253 (by decide) v hb
def cl_2254 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,true),(52,false),(56,false)]
theorem inp_2254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2254 (by decide) v hb
def cl_2255 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,true),(52,false),(56,false)]
theorem inp_2255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2255 (by decide) v hb
def cl_2257 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,true),(56,false)]
theorem inp_2257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2257 (by decide) v hb
def cl_2258 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,true),(56,false)]
theorem inp_2258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2258 (by decide) v hb
def cl_2259 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,true),(56,false)]
theorem inp_2259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2259 v hb
def cl_2261 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,true),(56,false)]
theorem inp_2261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2261 (by decide) v hb
def cl_2262 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,true),(56,false)]
theorem inp_2262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2262 (by decide) v hb
def cl_2263 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,true),(56,false)]
theorem inp_2263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2263 v hb
def cl_2266 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,true),(56,false)]
theorem inp_2266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2266 (by decide) v hb
def cl_2267 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,true),(56,false)]
theorem inp_2267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2267 v hb
def cl_2272 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,true),(52,true),(56,false)]
theorem inp_2272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2272 (by decide) v hb
def cl_2273 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,false),(56,true)]
theorem inp_2273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2273 (by decide) v hb
def cl_2274 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,false),(56,true)]
theorem inp_2274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2274 (by decide) v hb
def cl_2275 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,false),(56,true)]
theorem inp_2275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2275 v hb
def cl_2276 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,false),(52,false),(56,true)]
theorem inp_2276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2276 v hb
def cl_2277 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,false),(56,true)]
theorem inp_2277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2277 (by decide) v hb
def cl_2278 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,false),(56,true)]
theorem inp_2278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2278 (by decide) v hb
def cl_2279 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,false),(56,true)]
theorem inp_2279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2279 (by decide) v hb
def cl_2280 : CNF.NClause := [(97,true),(32,true),(37,true),(42,true),(47,false),(52,false),(56,true)]
theorem inp_2280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2280 (by decide) v hb
def cl_2281 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,true),(52,false),(56,true)]
theorem inp_2281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2281 (by decide) v hb
def cl_2282 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,false),(56,true)]
theorem inp_2282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2282 (by decide) v hb
def cl_2283 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,false),(56,true)]
theorem inp_2283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2283 (by decide) v hb
def cl_2284 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,true),(52,false),(56,true)]
theorem inp_2284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2284 (by decide) v hb
def cl_2285 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,true),(52,false),(56,true)]
theorem inp_2285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2285 (by decide) v hb
def cl_2286 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,true),(52,false),(56,true)]
theorem inp_2286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2286 (by decide) v hb
def cl_2287 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,true),(52,false),(56,true)]
theorem inp_2287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2287 (by decide) v hb
def cl_2288 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,true),(52,false),(56,true)]
theorem inp_2288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2288 (by decide) v hb
end Percolation.NReplay
