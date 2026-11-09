import NInputs036
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2442 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,false),(58,false)]
theorem inp_2442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2442 (by decide) v hb
def cl_2443 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,false),(58,false)]
theorem inp_2443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2443 (by decide) v hb
def cl_2444 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,true),(51,false),(58,false)]
theorem inp_2444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2444 (by decide) v hb
def cl_2445 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,false),(58,false)]
theorem inp_2445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2445 (by decide) v hb
def cl_2446 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,true),(51,false),(58,false)]
theorem inp_2446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2446 (by decide) v hb
def cl_2447 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,true),(51,false),(58,false)]
theorem inp_2447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2447 (by decide) v hb
def cl_2448 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,true),(51,false),(58,false)]
theorem inp_2448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2448 (by decide) v hb
def cl_2449 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,true),(58,false)]
theorem inp_2449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2449 v hb
def cl_2450 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,true),(58,false)]
theorem inp_2450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2450 (by decide) v hb
def cl_2451 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,true),(58,false)]
theorem inp_2451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2451 (by decide) v hb
def cl_2452 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,true),(58,false)]
theorem inp_2452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2452 (by decide) v hb
def cl_2453 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,true),(58,false)]
theorem inp_2453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2453 v hb
def cl_2454 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,true),(58,false)]
theorem inp_2454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2454 (by decide) v hb
def cl_2455 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,true),(58,false)]
theorem inp_2455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2455 (by decide) v hb
def cl_2456 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,true),(58,false)]
theorem inp_2456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2456 (by decide) v hb
def cl_2457 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,true),(58,false)]
theorem inp_2457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2457 (by decide) v hb
def cl_2458 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,true),(58,false)]
theorem inp_2458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2458 (by decide) v hb
def cl_2459 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,true),(58,false)]
theorem inp_2459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2459 (by decide) v hb
def cl_2460 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,true),(51,true),(58,false)]
theorem inp_2460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2460 (by decide) v hb
def cl_2461 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,true),(58,false)]
theorem inp_2461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2461 (by decide) v hb
def cl_2462 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,true),(51,true),(58,false)]
theorem inp_2462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2462 (by decide) v hb
def cl_2463 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,true),(51,true),(58,false)]
theorem inp_2463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2463 (by decide) v hb
def cl_2464 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,true),(51,true),(58,false)]
theorem inp_2464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2464 (by decide) v hb
def cl_2465 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,false),(58,true)]
theorem inp_2465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2465 (by decide) v hb
def cl_2466 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,false),(58,true)]
theorem inp_2466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2466 (by decide) v hb
def cl_2467 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,false),(58,true)]
theorem inp_2467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2467 v hb
def cl_2468 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,false),(58,true)]
theorem inp_2468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2468 v hb
def cl_2469 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,false),(58,true)]
theorem inp_2469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2469 (by decide) v hb
def cl_2470 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,false),(58,true)]
theorem inp_2470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2470 (by decide) v hb
def cl_2471 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,false),(58,true)]
theorem inp_2471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2471 v hb
def cl_2472 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,false),(58,true)]
theorem inp_2472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2472 v hb
def cl_2473 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,false),(58,true)]
theorem inp_2473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2473 (by decide) v hb
def cl_2474 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,false),(58,true)]
theorem inp_2474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2474 (by decide) v hb
def cl_2475 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,false),(58,true)]
theorem inp_2475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2475 v hb
def cl_2476 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,true),(51,false),(58,true)]
theorem inp_2476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2476 (by decide) v hb
def cl_2477 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,false),(58,true)]
theorem inp_2477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2477 (by decide) v hb
def cl_2478 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,true),(51,false),(58,true)]
theorem inp_2478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2478 (by decide) v hb
def cl_2479 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,true),(51,false),(58,true)]
theorem inp_2479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2479 (by decide) v hb
def cl_2480 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,true),(51,false),(58,true)]
theorem inp_2480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2480 (by decide) v hb
def cl_2481 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,true),(58,true)]
theorem inp_2481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2481 v hb
def cl_2482 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,true),(58,true)]
theorem inp_2482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2482 (by decide) v hb
def cl_2483 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,true),(58,true)]
theorem inp_2483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2483 v hb
def cl_2484 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,true),(58,true)]
theorem inp_2484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2484 v hb
def cl_2485 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,true),(58,true)]
theorem inp_2485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2485 v hb
def cl_2486 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,true),(58,true)]
theorem inp_2486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2486 (by decide) v hb
def cl_2487 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,true),(58,true)]
theorem inp_2487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2487 v hb
def cl_2488 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,false),(51,true),(58,true)]
theorem inp_2488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2488 (by decide) v hb
def cl_2489 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,true),(58,true)]
theorem inp_2489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2489 v hb
def cl_2490 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,true),(58,true)]
theorem inp_2490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2490 (by decide) v hb
def cl_2491 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,true),(58,true)]
theorem inp_2491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2491 v hb
end Percolation.NReplay
