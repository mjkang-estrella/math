import NInputs039
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2592 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,true),(51,true),(57,false)]
theorem inp_2592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2592 (by decide) v hb
def cl_2593 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,false),(57,true)]
theorem inp_2593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2593 (by decide) v hb
def cl_2594 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,false),(57,true)]
theorem inp_2594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2594 (by decide) v hb
def cl_2595 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,false),(57,true)]
theorem inp_2595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2595 v hb
def cl_2596 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,false),(57,true)]
theorem inp_2596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2596 (by decide) v hb
def cl_2597 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,false),(57,true)]
theorem inp_2597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2597 (by decide) v hb
def cl_2598 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,false),(57,true)]
theorem inp_2598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2598 (by decide) v hb
def cl_2599 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,false),(57,true)]
theorem inp_2599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2599 v hb
def cl_2600 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,false),(51,false),(57,true)]
theorem inp_2600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2600 (by decide) v hb
def cl_2601 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,false),(57,true)]
theorem inp_2601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2601 (by decide) v hb
def cl_2602 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,false),(57,true)]
theorem inp_2602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2602 (by decide) v hb
def cl_2603 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,false),(57,true)]
theorem inp_2603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2603 v hb
def cl_2604 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,true),(51,false),(57,true)]
theorem inp_2604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2604 (by decide) v hb
def cl_2605 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,false),(57,true)]
theorem inp_2605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2605 (by decide) v hb
def cl_2606 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,true),(51,false),(57,true)]
theorem inp_2606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2606 (by decide) v hb
def cl_2607 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,true),(51,false),(57,true)]
theorem inp_2607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2607 (by decide) v hb
def cl_2608 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,true),(51,false),(57,true)]
theorem inp_2608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2608 (by decide) v hb
def cl_2609 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,true),(57,true)]
theorem inp_2609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2609 (by decide) v hb
def cl_2610 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,true),(57,true)]
theorem inp_2610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2610 (by decide) v hb
def cl_2611 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,true),(57,true)]
theorem inp_2611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2611 v hb
def cl_2612 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,true),(57,true)]
theorem inp_2612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2612 (by decide) v hb
def cl_2613 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,true),(57,true)]
theorem inp_2613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2613 (by decide) v hb
def cl_2614 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,true),(57,true)]
theorem inp_2614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2614 (by decide) v hb
def cl_2615 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,true),(57,true)]
theorem inp_2615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2615 v hb
def cl_2616 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,false),(51,true),(57,true)]
theorem inp_2616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2616 (by decide) v hb
def cl_2617 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,true),(57,true)]
theorem inp_2617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2617 (by decide) v hb
def cl_2618 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,true),(57,true)]
theorem inp_2618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2618 (by decide) v hb
def cl_2619 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,true),(57,true)]
theorem inp_2619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2619 v hb
def cl_2620 : CNF.NClause := [(102,false),(32,true),(38,true),(44,false),(50,true),(51,true),(57,true)]
theorem inp_2620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2620 (by decide) v hb
def cl_2621 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,true),(57,true)]
theorem inp_2621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2621 (by decide) v hb
def cl_2622 : CNF.NClause := [(102,false),(32,true),(38,false),(44,true),(50,true),(51,true),(57,true)]
theorem inp_2622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2622 (by decide) v hb
def cl_2623 : CNF.NClause := [(102,false),(32,false),(38,true),(44,true),(50,true),(51,true),(57,true)]
theorem inp_2623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2623 (by decide) v hb
def cl_2624 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,true),(51,true),(57,true)]
theorem inp_2624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2624 (by decide) v hb
def cl_2625 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2625 v hb
def cl_2626 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2626 v hb
def cl_2627 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2627 v hb
def cl_2628 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2628 v hb
def cl_2629 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2629 v hb
def cl_2630 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2630 v hb
def cl_2631 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2631 v hb
def cl_2632 : CNF.NClause := [(103,true),(41,true),(42,true),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2632 v hb
def cl_2633 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,false),(61,false)]
theorem inp_2633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2633 (by decide) v hb
def cl_2634 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,false),(61,false)]
theorem inp_2634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2634 (by decide) v hb
def cl_2635 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,false),(61,false)]
theorem inp_2635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2635 (by decide) v hb
def cl_2636 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,true),(45,false),(61,false)]
theorem inp_2636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2636 (by decide) v hb
def cl_2637 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,false),(61,false)]
theorem inp_2637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2637 (by decide) v hb
def cl_2638 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,true),(45,false),(61,false)]
theorem inp_2638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2638 (by decide) v hb
def cl_2639 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,true),(45,false),(61,false)]
theorem inp_2639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2639 (by decide) v hb
def cl_2640 : CNF.NClause := [(103,true),(41,true),(42,true),(43,true),(44,true),(45,false),(61,false)]
theorem inp_2640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2640 (by decide) v hb
def cl_2641 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,true),(61,false)]
theorem inp_2641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2641 v hb
end Percolation.NReplay
