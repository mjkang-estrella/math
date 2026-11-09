import NInputs034
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2342 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,false),(61,true)]
theorem inp_2342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2342 (by decide) v hb
def cl_2343 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,false),(61,true)]
theorem inp_2343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2343 v hb
def cl_2344 : CNF.NClause := [(98,true),(51,true),(52,true),(53,true),(54,false),(55,false),(61,true)]
theorem inp_2344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2344 (by decide) v hb
def cl_2345 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,false),(61,true)]
theorem inp_2345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2345 (by decide) v hb
def cl_2346 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,false),(61,true)]
theorem inp_2346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2346 (by decide) v hb
def cl_2347 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,false),(61,true)]
theorem inp_2347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2347 (by decide) v hb
def cl_2348 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,true),(55,false),(61,true)]
theorem inp_2348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2348 (by decide) v hb
def cl_2349 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,false),(61,true)]
theorem inp_2349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2349 (by decide) v hb
def cl_2350 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,true),(55,false),(61,true)]
theorem inp_2350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2350 (by decide) v hb
def cl_2351 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,true),(55,false),(61,true)]
theorem inp_2351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2351 (by decide) v hb
def cl_2352 : CNF.NClause := [(98,false),(51,true),(52,true),(53,true),(54,true),(55,false),(61,true)]
theorem inp_2352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2352 (by decide) v hb
def cl_2353 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,true),(61,true)]
theorem inp_2353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2353 (by decide) v hb
def cl_2354 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,true),(61,true)]
theorem inp_2354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2354 (by decide) v hb
def cl_2355 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,true),(61,true)]
theorem inp_2355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2355 (by decide) v hb
def cl_2356 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,true),(61,true)]
theorem inp_2356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2356 (by decide) v hb
def cl_2357 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,true),(61,true)]
theorem inp_2357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2357 (by decide) v hb
def cl_2358 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,true),(61,true)]
theorem inp_2358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2358 (by decide) v hb
def cl_2359 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,true),(61,true)]
theorem inp_2359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2359 v hb
def cl_2360 : CNF.NClause := [(98,false),(51,true),(52,true),(53,true),(54,false),(55,true),(61,true)]
theorem inp_2360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2360 (by decide) v hb
def cl_2361 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,true),(61,true)]
theorem inp_2361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2361 (by decide) v hb
def cl_2362 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,true),(61,true)]
theorem inp_2362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2362 (by decide) v hb
def cl_2363 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,true),(61,true)]
theorem inp_2363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2363 (by decide) v hb
def cl_2364 : CNF.NClause := [(98,false),(51,true),(52,true),(53,false),(54,true),(55,true),(61,true)]
theorem inp_2364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2364 (by decide) v hb
def cl_2365 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,true),(61,true)]
theorem inp_2365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2365 (by decide) v hb
def cl_2366 : CNF.NClause := [(98,false),(51,true),(52,false),(53,true),(54,true),(55,true),(61,true)]
theorem inp_2366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2366 (by decide) v hb
def cl_2367 : CNF.NClause := [(98,false),(51,false),(52,true),(53,true),(54,true),(55,true),(61,true)]
theorem inp_2367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2367 (by decide) v hb
def cl_2368 : CNF.NClause := [(98,false),(51,true),(52,true),(53,true),(54,true),(55,true),(61,true)]
theorem inp_2368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) cl_2368 (by decide) v hb
def cl_2369 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2369 v hb
def cl_2370 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2370 v hb
def cl_2371 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2371 v hb
def cl_2372 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,false),(60,false)]
theorem inp_2372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2372 v hb
def cl_2373 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,false),(60,false)]
theorem inp_2373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2373 v hb
def cl_2374 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,false),(60,false)]
theorem inp_2374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2374 v hb
def cl_2375 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,false),(60,false)]
theorem inp_2375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2375 (by decide) v hb
def cl_2376 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,false),(51,false),(60,false)]
theorem inp_2376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2376 (by decide) v hb
def cl_2377 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,false),(60,false)]
theorem inp_2377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2377 v hb
def cl_2378 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,false),(60,false)]
theorem inp_2378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2378 (by decide) v hb
def cl_2379 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,false),(60,false)]
theorem inp_2379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2379 v hb
def cl_2380 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,true),(51,false),(60,false)]
theorem inp_2380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2380 (by decide) v hb
def cl_2381 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,false),(60,false)]
theorem inp_2381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2381 (by decide) v hb
def cl_2382 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,true),(51,false),(60,false)]
theorem inp_2382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2382 (by decide) v hb
def cl_2383 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,false),(60,false)]
theorem inp_2383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2383 v hb
def cl_2384 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,true),(51,false),(60,false)]
theorem inp_2384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2384 (by decide) v hb
def cl_2385 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,true),(60,false)]
theorem inp_2385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2385 (by decide) v hb
def cl_2386 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,true),(60,false)]
theorem inp_2386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2386 (by decide) v hb
def cl_2387 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,true),(60,false)]
theorem inp_2387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2387 (by decide) v hb
def cl_2388 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,true),(60,false)]
theorem inp_2388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2388 (by decide) v hb
def cl_2389 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,true),(60,false)]
theorem inp_2389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2389 (by decide) v hb
def cl_2390 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,true),(60,false)]
theorem inp_2390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2390 (by decide) v hb
def cl_2391 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,true),(60,false)]
theorem inp_2391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2391 (by decide) v hb
end Percolation.NReplay
