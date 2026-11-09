import NInputs033
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2289 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,true),(56,true)]
theorem inp_2289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2289 (by decide) v hb
def cl_2290 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,true),(56,true)]
theorem inp_2290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2290 (by decide) v hb
def cl_2291 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,true),(56,true)]
theorem inp_2291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2291 v hb
def cl_2292 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,false),(52,true),(56,true)]
theorem inp_2292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2292 (by decide) v hb
def cl_2293 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,true),(56,true)]
theorem inp_2293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2293 (by decide) v hb
def cl_2294 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,true),(56,true)]
theorem inp_2294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2294 (by decide) v hb
def cl_2295 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,true),(56,true)]
theorem inp_2295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2295 (by decide) v hb
def cl_2296 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,false),(52,true),(56,true)]
theorem inp_2296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2296 (by decide) v hb
def cl_2297 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,true),(52,true),(56,true)]
theorem inp_2297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2297 (by decide) v hb
def cl_2298 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,true),(56,true)]
theorem inp_2298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2298 (by decide) v hb
def cl_2299 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,true),(56,true)]
theorem inp_2299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2299 v hb
def cl_2300 : CNF.NClause := [(97,false),(32,true),(37,true),(42,false),(47,true),(52,true),(56,true)]
theorem inp_2300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2300 (by decide) v hb
def cl_2301 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,true),(52,true),(56,true)]
theorem inp_2301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2301 (by decide) v hb
def cl_2302 : CNF.NClause := [(97,false),(32,true),(37,false),(42,true),(47,true),(52,true),(56,true)]
theorem inp_2302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2302 (by decide) v hb
def cl_2303 : CNF.NClause := [(97,false),(32,false),(37,true),(42,true),(47,true),(52,true),(56,true)]
theorem inp_2303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2303 (by decide) v hb
def cl_2304 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,true),(52,true),(56,true)]
theorem inp_2304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) cl_2304 (by decide) v hb
def cl_2305 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,false),(61,false)]
theorem inp_2305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2305 (by decide) v hb
def cl_2306 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,false),(61,false)]
theorem inp_2306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2306 (by decide) v hb
def cl_2307 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,false),(61,false)]
theorem inp_2307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2307 (by decide) v hb
def cl_2308 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,false),(61,false)]
theorem inp_2308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2308 (by decide) v hb
def cl_2309 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,false),(61,false)]
theorem inp_2309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2309 (by decide) v hb
def cl_2310 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,false),(61,false)]
theorem inp_2310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2310 (by decide) v hb
def cl_2311 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,false),(61,false)]
theorem inp_2311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2311 (by decide) v hb
def cl_2312 : CNF.NClause := [(98,true),(51,true),(52,true),(53,true),(54,false),(55,false),(61,false)]
theorem inp_2312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2312 (by decide) v hb
def cl_2313 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,false),(61,false)]
theorem inp_2313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2313 (by decide) v hb
def cl_2314 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,false),(61,false)]
theorem inp_2314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2314 (by decide) v hb
def cl_2315 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,false),(61,false)]
theorem inp_2315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2315 (by decide) v hb
def cl_2316 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,true),(55,false),(61,false)]
theorem inp_2316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2316 (by decide) v hb
def cl_2317 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,false),(61,false)]
theorem inp_2317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2317 (by decide) v hb
def cl_2318 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,true),(55,false),(61,false)]
theorem inp_2318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2318 (by decide) v hb
def cl_2319 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,true),(55,false),(61,false)]
theorem inp_2319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2319 (by decide) v hb
def cl_2321 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,true),(61,false)]
theorem inp_2321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2321 (by decide) v hb
def cl_2322 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,true),(61,false)]
theorem inp_2322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2322 (by decide) v hb
def cl_2323 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,true),(61,false)]
theorem inp_2323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2323 (by decide) v hb
def cl_2324 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,true),(61,false)]
theorem inp_2324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2324 (by decide) v hb
def cl_2325 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,true),(61,false)]
theorem inp_2325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2325 (by decide) v hb
def cl_2326 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,true),(61,false)]
theorem inp_2326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2326 (by decide) v hb
def cl_2327 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,true),(61,false)]
theorem inp_2327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2327 (by decide) v hb
def cl_2328 : CNF.NClause := [(98,true),(51,true),(52,true),(53,true),(54,false),(55,true),(61,false)]
theorem inp_2328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2328 (by decide) v hb
def cl_2329 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,true),(61,false)]
theorem inp_2329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2329 (by decide) v hb
def cl_2330 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,true),(61,false)]
theorem inp_2330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2330 (by decide) v hb
def cl_2331 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,true),(61,false)]
theorem inp_2331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2331 (by decide) v hb
def cl_2332 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,true),(55,true),(61,false)]
theorem inp_2332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2332 (by decide) v hb
def cl_2333 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,true),(61,false)]
theorem inp_2333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2333 (by decide) v hb
def cl_2335 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,true),(55,true),(61,false)]
theorem inp_2335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2335 (by decide) v hb
def cl_2337 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,false),(61,true)]
theorem inp_2337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2337 (by decide) v hb
def cl_2338 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,false),(61,true)]
theorem inp_2338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2338 (by decide) v hb
def cl_2339 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,false),(61,true)]
theorem inp_2339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2339 (by decide) v hb
def cl_2340 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,false),(61,true)]
theorem inp_2340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2340 (by decide) v hb
def cl_2341 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,false),(61,true)]
theorem inp_2341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2341 (by decide) v hb
end Percolation.NReplay
