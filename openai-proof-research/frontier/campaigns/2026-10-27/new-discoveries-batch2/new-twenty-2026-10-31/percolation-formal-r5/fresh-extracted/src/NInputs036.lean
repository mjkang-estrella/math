import NInputs035
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2392 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,false),(51,true),(60,false)]
theorem inp_2392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2392 (by decide) v hb
def cl_2393 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,true),(60,false)]
theorem inp_2393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2393 v hb
def cl_2394 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,true),(60,false)]
theorem inp_2394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2394 (by decide) v hb
def cl_2395 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,true),(60,false)]
theorem inp_2395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2395 v hb
def cl_2396 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,true),(51,true),(60,false)]
theorem inp_2396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2396 (by decide) v hb
def cl_2397 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,true),(60,false)]
theorem inp_2397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2397 (by decide) v hb
def cl_2398 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,true),(51,true),(60,false)]
theorem inp_2398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2398 (by decide) v hb
def cl_2399 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,true),(60,false)]
theorem inp_2399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2399 v hb
def cl_2400 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,true),(51,true),(60,false)]
theorem inp_2400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2400 (by decide) v hb
def cl_2401 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,false),(60,true)]
theorem inp_2401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2401 v hb
def cl_2402 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,false),(60,true)]
theorem inp_2402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2402 v hb
def cl_2403 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,false),(60,true)]
theorem inp_2403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2403 (by decide) v hb
def cl_2404 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,false),(60,true)]
theorem inp_2404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2404 (by decide) v hb
def cl_2405 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,false),(60,true)]
theorem inp_2405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2405 (by decide) v hb
def cl_2406 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,false),(60,true)]
theorem inp_2406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2406 (by decide) v hb
def cl_2407 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,false),(60,true)]
theorem inp_2407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2407 v hb
def cl_2408 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,false),(51,false),(60,true)]
theorem inp_2408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2408 (by decide) v hb
def cl_2409 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,false),(60,true)]
theorem inp_2409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2409 v hb
def cl_2410 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,false),(60,true)]
theorem inp_2410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2410 (by decide) v hb
def cl_2411 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,false),(60,true)]
theorem inp_2411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2411 v hb
def cl_2412 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,true),(51,false),(60,true)]
theorem inp_2412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2412 (by decide) v hb
def cl_2413 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,false),(60,true)]
theorem inp_2413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2413 (by decide) v hb
def cl_2414 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,true),(51,false),(60,true)]
theorem inp_2414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2414 (by decide) v hb
def cl_2415 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,false),(60,true)]
theorem inp_2415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2415 v hb
def cl_2416 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,true),(51,false),(60,true)]
theorem inp_2416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2416 (by decide) v hb
def cl_2417 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,true),(60,true)]
theorem inp_2417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2417 (by decide) v hb
def cl_2418 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,true),(60,true)]
theorem inp_2418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2418 (by decide) v hb
def cl_2419 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,true),(60,true)]
theorem inp_2419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2419 (by decide) v hb
def cl_2420 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,true),(60,true)]
theorem inp_2420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2420 (by decide) v hb
def cl_2421 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,true),(60,true)]
theorem inp_2421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2421 (by decide) v hb
def cl_2422 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,true),(60,true)]
theorem inp_2422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2422 (by decide) v hb
def cl_2423 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,true),(60,true)]
theorem inp_2423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2423 (by decide) v hb
def cl_2424 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,false),(51,true),(60,true)]
theorem inp_2424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2424 (by decide) v hb
def cl_2425 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,true),(60,true)]
theorem inp_2425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2425 v hb
def cl_2426 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,true),(60,true)]
theorem inp_2426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2426 (by decide) v hb
def cl_2427 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,true),(60,true)]
theorem inp_2427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2427 v hb
def cl_2428 : CNF.NClause := [(99,false),(35,true),(39,true),(43,false),(47,true),(51,true),(60,true)]
theorem inp_2428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2428 (by decide) v hb
def cl_2429 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,true),(60,true)]
theorem inp_2429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2429 (by decide) v hb
def cl_2430 : CNF.NClause := [(99,false),(35,true),(39,false),(43,true),(47,true),(51,true),(60,true)]
theorem inp_2430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2430 (by decide) v hb
def cl_2431 : CNF.NClause := [(99,false),(35,false),(39,true),(43,true),(47,true),(51,true),(60,true)]
theorem inp_2431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2431 (by decide) v hb
def cl_2432 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,true),(51,true),(60,true)]
theorem inp_2432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2432 (by decide) v hb
def cl_2433 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,false),(58,false)]
theorem inp_2433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2433 v hb
def cl_2434 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,false),(58,false)]
theorem inp_2434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2434 (by decide) v hb
def cl_2435 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,false),(58,false)]
theorem inp_2435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2435 v hb
def cl_2436 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,false),(58,false)]
theorem inp_2436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2436 (by decide) v hb
def cl_2437 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,false),(58,false)]
theorem inp_2437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2437 v hb
def cl_2438 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,false),(58,false)]
theorem inp_2438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2438 (by decide) v hb
def cl_2439 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,false),(58,false)]
theorem inp_2439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2439 (by decide) v hb
def cl_2440 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,false),(58,false)]
theorem inp_2440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2440 v hb
def cl_2441 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,false),(58,false)]
theorem inp_2441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2441 (by decide) v hb
end Percolation.NReplay
