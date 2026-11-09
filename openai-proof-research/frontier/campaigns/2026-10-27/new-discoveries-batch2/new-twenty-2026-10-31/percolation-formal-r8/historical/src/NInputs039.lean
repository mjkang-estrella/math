import NInputs038
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2542 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,true),(51,false),(59,true)]
theorem inp_2542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2542 (by decide) v hb
def cl_2543 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,true),(51,false),(59,true)]
theorem inp_2543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2543 (by decide) v hb
def cl_2544 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,true),(51,false),(59,true)]
theorem inp_2544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2544 (by decide) v hb
def cl_2545 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,true),(59,true)]
theorem inp_2545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2545 (by decide) v hb
def cl_2546 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,true),(59,true)]
theorem inp_2546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2546 (by decide) v hb
def cl_2547 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,true),(59,true)]
theorem inp_2547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2547 v hb
def cl_2548 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,true),(59,true)]
theorem inp_2548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2548 v hb
def cl_2549 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,true),(59,true)]
theorem inp_2549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2549 (by decide) v hb
def cl_2550 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,true),(59,true)]
theorem inp_2550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2550 (by decide) v hb
def cl_2551 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,true),(59,true)]
theorem inp_2551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2551 (by decide) v hb
def cl_2552 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,false),(51,true),(59,true)]
theorem inp_2552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2552 (by decide) v hb
def cl_2553 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,true),(59,true)]
theorem inp_2553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2553 (by decide) v hb
def cl_2554 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,true),(59,true)]
theorem inp_2554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2554 (by decide) v hb
def cl_2555 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,true),(59,true)]
theorem inp_2555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2555 (by decide) v hb
def cl_2556 : CNF.NClause := [(101,false),(34,true),(37,true),(45,false),(48,true),(51,true),(59,true)]
theorem inp_2556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2556 (by decide) v hb
def cl_2557 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,true),(59,true)]
theorem inp_2557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2557 (by decide) v hb
def cl_2558 : CNF.NClause := [(101,false),(34,true),(37,false),(45,true),(48,true),(51,true),(59,true)]
theorem inp_2558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2558 (by decide) v hb
def cl_2559 : CNF.NClause := [(101,false),(34,false),(37,true),(45,true),(48,true),(51,true),(59,true)]
theorem inp_2559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2559 (by decide) v hb
def cl_2560 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,true),(51,true),(59,true)]
theorem inp_2560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2560 (by decide) v hb
def cl_2561 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,false),(57,false)]
theorem inp_2561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2561 (by decide) v hb
def cl_2562 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,false),(57,false)]
theorem inp_2562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2562 (by decide) v hb
def cl_2563 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,false),(57,false)]
theorem inp_2563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2563 v hb
def cl_2564 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,false),(57,false)]
theorem inp_2564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2564 v hb
def cl_2565 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,false),(57,false)]
theorem inp_2565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2565 (by decide) v hb
def cl_2566 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,false),(57,false)]
theorem inp_2566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2566 (by decide) v hb
def cl_2567 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,false),(57,false)]
theorem inp_2567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2567 (by decide) v hb
def cl_2568 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,false),(51,false),(57,false)]
theorem inp_2568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2568 (by decide) v hb
def cl_2569 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,false),(57,false)]
theorem inp_2569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2569 (by decide) v hb
def cl_2570 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,false),(57,false)]
theorem inp_2570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2570 (by decide) v hb
def cl_2571 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,false),(57,false)]
theorem inp_2571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2571 (by decide) v hb
def cl_2572 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,true),(51,false),(57,false)]
theorem inp_2572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2572 (by decide) v hb
def cl_2573 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,false),(57,false)]
theorem inp_2573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2573 (by decide) v hb
def cl_2574 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,true),(51,false),(57,false)]
theorem inp_2574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2574 (by decide) v hb
def cl_2575 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,true),(51,false),(57,false)]
theorem inp_2575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2575 (by decide) v hb
def cl_2576 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,true),(51,false),(57,false)]
theorem inp_2576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2576 (by decide) v hb
def cl_2577 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,true),(57,false)]
theorem inp_2577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2577 (by decide) v hb
def cl_2578 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,true),(57,false)]
theorem inp_2578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2578 (by decide) v hb
def cl_2579 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,true),(57,false)]
theorem inp_2579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2579 v hb
def cl_2580 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,true),(57,false)]
theorem inp_2580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2580 (by decide) v hb
def cl_2581 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,true),(57,false)]
theorem inp_2581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2581 (by decide) v hb
def cl_2582 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,true),(57,false)]
theorem inp_2582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2582 (by decide) v hb
def cl_2583 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,true),(57,false)]
theorem inp_2583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2583 (by decide) v hb
def cl_2584 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,false),(51,true),(57,false)]
theorem inp_2584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2584 (by decide) v hb
def cl_2585 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,true),(57,false)]
theorem inp_2585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2585 (by decide) v hb
def cl_2586 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,true),(57,false)]
theorem inp_2586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2586 (by decide) v hb
def cl_2587 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,true),(57,false)]
theorem inp_2587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2587 (by decide) v hb
def cl_2588 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,true),(51,true),(57,false)]
theorem inp_2588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2588 (by decide) v hb
def cl_2589 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,true),(57,false)]
theorem inp_2589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2589 (by decide) v hb
def cl_2590 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,true),(51,true),(57,false)]
theorem inp_2590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2590 (by decide) v hb
def cl_2591 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,true),(51,true),(57,false)]
theorem inp_2591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2591 (by decide) v hb
end Percolation.NReplay
