import NInputs040
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2642 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,true),(61,false)]
theorem inp_2642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2642 (by decide) v hb
def cl_2643 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,true),(61,false)]
theorem inp_2643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2643 (by decide) v hb
def cl_2645 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,true),(61,false)]
theorem inp_2645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2645 (by decide) v hb
def cl_2646 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,true),(61,false)]
theorem inp_2646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2646 (by decide) v hb
def cl_2647 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,true),(61,false)]
theorem inp_2647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2647 (by decide) v hb
def cl_2649 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,true),(61,false)]
theorem inp_2649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2649 (by decide) v hb
def cl_2650 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,true),(61,false)]
theorem inp_2650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2650 (by decide) v hb
def cl_2651 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,true),(61,false)]
theorem inp_2651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2651 (by decide) v hb
def cl_2653 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,true),(61,false)]
theorem inp_2653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2653 (by decide) v hb
def cl_2655 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,true),(45,true),(61,false)]
theorem inp_2655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2655 (by decide) v hb
def cl_2657 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2657 v hb
def cl_2658 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2658 v hb
def cl_2659 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2659 v hb
def cl_2660 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2660 v hb
def cl_2661 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,false),(61,true)]
theorem inp_2661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2661 (by decide) v hb
def cl_2662 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,false),(61,true)]
theorem inp_2662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2662 v hb
def cl_2663 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,false),(61,true)]
theorem inp_2663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2663 (by decide) v hb
def cl_2664 : CNF.NClause := [(103,true),(41,true),(42,true),(43,true),(44,false),(45,false),(61,true)]
theorem inp_2664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2664 (by decide) v hb
def cl_2665 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,false),(61,true)]
theorem inp_2665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2665 (by decide) v hb
def cl_2666 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,false),(61,true)]
theorem inp_2666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2666 v hb
def cl_2667 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,false),(61,true)]
theorem inp_2667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2667 (by decide) v hb
def cl_2668 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,true),(45,false),(61,true)]
theorem inp_2668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2668 (by decide) v hb
def cl_2669 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,false),(61,true)]
theorem inp_2669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2669 (by decide) v hb
def cl_2670 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,true),(45,false),(61,true)]
theorem inp_2670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2670 v hb
def cl_2671 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,true),(45,false),(61,true)]
theorem inp_2671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2671 (by decide) v hb
def cl_2672 : CNF.NClause := [(103,false),(41,true),(42,true),(43,true),(44,true),(45,false),(61,true)]
theorem inp_2672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2672 (by decide) v hb
def cl_2673 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,true),(61,true)]
theorem inp_2673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2673 (by decide) v hb
def cl_2674 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,true),(61,true)]
theorem inp_2674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2674 (by decide) v hb
def cl_2675 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,true),(61,true)]
theorem inp_2675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2675 (by decide) v hb
def cl_2676 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,true),(61,true)]
theorem inp_2676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2676 (by decide) v hb
def cl_2677 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,true),(61,true)]
theorem inp_2677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2677 (by decide) v hb
def cl_2678 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,true),(61,true)]
theorem inp_2678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2678 (by decide) v hb
def cl_2679 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,true),(61,true)]
theorem inp_2679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2679 (by decide) v hb
def cl_2680 : CNF.NClause := [(103,false),(41,true),(42,true),(43,true),(44,false),(45,true),(61,true)]
theorem inp_2680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2680 (by decide) v hb
def cl_2681 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,true),(61,true)]
theorem inp_2681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2681 (by decide) v hb
def cl_2682 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,true),(61,true)]
theorem inp_2682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2682 (by decide) v hb
def cl_2683 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,true),(61,true)]
theorem inp_2683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2683 (by decide) v hb
def cl_2684 : CNF.NClause := [(103,false),(41,true),(42,true),(43,false),(44,true),(45,true),(61,true)]
theorem inp_2684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2684 (by decide) v hb
def cl_2685 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,true),(61,true)]
theorem inp_2685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2685 (by decide) v hb
def cl_2686 : CNF.NClause := [(103,false),(41,true),(42,false),(43,true),(44,true),(45,true),(61,true)]
theorem inp_2686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2686 (by decide) v hb
def cl_2687 : CNF.NClause := [(103,false),(41,false),(42,true),(43,true),(44,true),(45,true),(61,true)]
theorem inp_2687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2687 (by decide) v hb
def cl_2688 : CNF.NClause := [(103,false),(41,true),(42,true),(43,true),(44,true),(45,true),(61,true)]
theorem inp_2688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2688 (by decide) v hb
def cl_2689 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,false),(59,false)]
theorem inp_2689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2689 (by decide) v hb
def cl_2690 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,false),(59,false)]
theorem inp_2690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2690 (by decide) v hb
def cl_2691 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,false),(59,false)]
theorem inp_2691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2691 v hb
def cl_2692 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,false),(59,false)]
theorem inp_2692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2692 v hb
def cl_2693 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,false),(59,false)]
theorem inp_2693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2693 (by decide) v hb
def cl_2694 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,false),(59,false)]
theorem inp_2694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2694 (by decide) v hb
def cl_2695 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,false),(59,false)]
theorem inp_2695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2695 v hb
def cl_2696 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,false),(59,false)]
theorem inp_2696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2696 v hb
end Percolation.NReplay
