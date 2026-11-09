import NInputs037
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2492 : CNF.NClause := [(100,false),(33,true),(40,true),(42,false),(49,true),(51,true),(58,true)]
theorem inp_2492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2492 (by decide) v hb
def cl_2493 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,true),(58,true)]
theorem inp_2493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2493 (by decide) v hb
def cl_2494 : CNF.NClause := [(100,false),(33,true),(40,false),(42,true),(49,true),(51,true),(58,true)]
theorem inp_2494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2494 (by decide) v hb
def cl_2495 : CNF.NClause := [(100,false),(33,false),(40,true),(42,true),(49,true),(51,true),(58,true)]
theorem inp_2495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2495 (by decide) v hb
def cl_2496 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,true),(51,true),(58,true)]
theorem inp_2496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2496 (by decide) v hb
def cl_2497 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,false),(59,false)]
theorem inp_2497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2497 v hb
def cl_2498 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,false),(59,false)]
theorem inp_2498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2498 (by decide) v hb
def cl_2499 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,false),(59,false)]
theorem inp_2499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2499 v hb
def cl_2500 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,false),(59,false)]
theorem inp_2500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2500 (by decide) v hb
def cl_2501 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,false),(59,false)]
theorem inp_2501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2501 (by decide) v hb
def cl_2502 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,false),(59,false)]
theorem inp_2502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2502 (by decide) v hb
def cl_2503 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,false),(59,false)]
theorem inp_2503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2503 (by decide) v hb
def cl_2504 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,false),(51,false),(59,false)]
theorem inp_2504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2504 (by decide) v hb
def cl_2505 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,false),(59,false)]
theorem inp_2505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2505 (by decide) v hb
def cl_2506 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,false),(59,false)]
theorem inp_2506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2506 (by decide) v hb
def cl_2507 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,false),(59,false)]
theorem inp_2507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2507 (by decide) v hb
def cl_2508 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,false),(59,false)]
theorem inp_2508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2508 v hb
def cl_2509 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,false),(59,false)]
theorem inp_2509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2509 (by decide) v hb
def cl_2510 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,true),(51,false),(59,false)]
theorem inp_2510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2510 (by decide) v hb
def cl_2511 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,true),(51,false),(59,false)]
theorem inp_2511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2511 (by decide) v hb
def cl_2512 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,true),(51,false),(59,false)]
theorem inp_2512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2512 (by decide) v hb
def cl_2513 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,true),(59,false)]
theorem inp_2513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2513 (by decide) v hb
def cl_2514 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,true),(59,false)]
theorem inp_2514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2514 (by decide) v hb
def cl_2515 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,true),(59,false)]
theorem inp_2515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2515 v hb
def cl_2516 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,true),(59,false)]
theorem inp_2516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2516 v hb
def cl_2517 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,true),(59,false)]
theorem inp_2517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2517 (by decide) v hb
def cl_2518 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,true),(59,false)]
theorem inp_2518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2518 (by decide) v hb
def cl_2519 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,true),(59,false)]
theorem inp_2519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2519 (by decide) v hb
def cl_2520 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,false),(51,true),(59,false)]
theorem inp_2520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2520 (by decide) v hb
def cl_2521 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,true),(59,false)]
theorem inp_2521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2521 (by decide) v hb
def cl_2522 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,true),(59,false)]
theorem inp_2522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2522 (by decide) v hb
def cl_2523 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,true),(59,false)]
theorem inp_2523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2523 (by decide) v hb
def cl_2524 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,true),(59,false)]
theorem inp_2524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2524 (by decide) v hb
def cl_2525 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,true),(59,false)]
theorem inp_2525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2525 (by decide) v hb
def cl_2526 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,true),(51,true),(59,false)]
theorem inp_2526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2526 (by decide) v hb
def cl_2527 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,true),(51,true),(59,false)]
theorem inp_2527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2527 (by decide) v hb
def cl_2528 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,true),(51,true),(59,false)]
theorem inp_2528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2528 (by decide) v hb
def cl_2529 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,false),(59,true)]
theorem inp_2529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2529 (by decide) v hb
def cl_2530 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,false),(59,true)]
theorem inp_2530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2530 (by decide) v hb
def cl_2531 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,false),(59,true)]
theorem inp_2531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2531 v hb
def cl_2532 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,false),(59,true)]
theorem inp_2532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2532 v hb
def cl_2533 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,false),(59,true)]
theorem inp_2533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2533 (by decide) v hb
def cl_2534 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,false),(59,true)]
theorem inp_2534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2534 (by decide) v hb
def cl_2535 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,false),(59,true)]
theorem inp_2535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2535 (by decide) v hb
def cl_2536 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,false),(51,false),(59,true)]
theorem inp_2536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2536 (by decide) v hb
def cl_2537 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,false),(59,true)]
theorem inp_2537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2537 (by decide) v hb
def cl_2538 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,false),(59,true)]
theorem inp_2538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2538 (by decide) v hb
def cl_2539 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,false),(59,true)]
theorem inp_2539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2539 (by decide) v hb
def cl_2540 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,false),(59,true)]
theorem inp_2540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2540 v hb
def cl_2541 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,false),(59,true)]
theorem inp_2541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2541 (by decide) v hb
end Percolation.NReplay
