import NInputs041
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2697 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,false),(59,false)]
theorem inp_2697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2697 (by decide) v hb
def cl_2698 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,false),(59,false)]
theorem inp_2698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2698 (by decide) v hb
def cl_2699 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,false),(59,false)]
theorem inp_2699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2699 (by decide) v hb
def cl_2700 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,false),(59,false)]
theorem inp_2700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2700 v hb
def cl_2701 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,false),(59,false)]
theorem inp_2701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2701 (by decide) v hb
def cl_2702 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,true),(52,false),(59,false)]
theorem inp_2702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2702 (by decide) v hb
def cl_2703 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,true),(52,false),(59,false)]
theorem inp_2703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2703 (by decide) v hb
def cl_2704 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,true),(52,false),(59,false)]
theorem inp_2704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2704 v hb
def cl_2705 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,true),(59,false)]
theorem inp_2705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2705 (by decide) v hb
def cl_2706 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,true),(59,false)]
theorem inp_2706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2706 (by decide) v hb
def cl_2707 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,true),(59,false)]
theorem inp_2707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2707 (by decide) v hb
def cl_2708 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,true),(59,false)]
theorem inp_2708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2708 v hb
def cl_2709 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,true),(59,false)]
theorem inp_2709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2709 (by decide) v hb
def cl_2710 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,true),(59,false)]
theorem inp_2710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2710 (by decide) v hb
def cl_2711 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,true),(59,false)]
theorem inp_2711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2711 v hb
def cl_2712 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,true),(59,false)]
theorem inp_2712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2712 v hb
def cl_2713 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,true),(59,false)]
theorem inp_2713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2713 (by decide) v hb
def cl_2714 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,true),(59,false)]
theorem inp_2714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2714 (by decide) v hb
def cl_2715 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,true),(59,false)]
theorem inp_2715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2715 (by decide) v hb
def cl_2716 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,true),(59,false)]
theorem inp_2716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2716 v hb
def cl_2717 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,true),(59,false)]
theorem inp_2717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2717 (by decide) v hb
def cl_2718 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,true),(52,true),(59,false)]
theorem inp_2718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2718 (by decide) v hb
def cl_2719 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,true),(52,true),(59,false)]
theorem inp_2719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2719 (by decide) v hb
def cl_2720 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,true),(52,true),(59,false)]
theorem inp_2720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2720 (by decide) v hb
def cl_2721 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,false),(59,true)]
theorem inp_2721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2721 (by decide) v hb
def cl_2722 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,false),(59,true)]
theorem inp_2722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2722 (by decide) v hb
def cl_2723 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,false),(59,true)]
theorem inp_2723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2723 (by decide) v hb
def cl_2724 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,false),(59,true)]
theorem inp_2724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2724 v hb
def cl_2725 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,false),(59,true)]
theorem inp_2725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2725 (by decide) v hb
def cl_2726 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,false),(59,true)]
theorem inp_2726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2726 (by decide) v hb
def cl_2727 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,false),(59,true)]
theorem inp_2727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2727 v hb
def cl_2728 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,false),(59,true)]
theorem inp_2728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2728 v hb
def cl_2729 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,false),(59,true)]
theorem inp_2729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2729 (by decide) v hb
def cl_2730 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,false),(59,true)]
theorem inp_2730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2730 (by decide) v hb
def cl_2731 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,false),(59,true)]
theorem inp_2731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2731 (by decide) v hb
def cl_2732 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,false),(59,true)]
theorem inp_2732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2732 v hb
def cl_2733 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,false),(59,true)]
theorem inp_2733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2733 (by decide) v hb
def cl_2734 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,true),(52,false),(59,true)]
theorem inp_2734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2734 (by decide) v hb
def cl_2735 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,true),(52,false),(59,true)]
theorem inp_2735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2735 (by decide) v hb
def cl_2736 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,true),(52,false),(59,true)]
theorem inp_2736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2736 (by decide) v hb
def cl_2737 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,true),(59,true)]
theorem inp_2737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2737 (by decide) v hb
def cl_2738 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,true),(59,true)]
theorem inp_2738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2738 (by decide) v hb
def cl_2739 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,true),(59,true)]
theorem inp_2739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2739 (by decide) v hb
def cl_2740 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,true),(59,true)]
theorem inp_2740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2740 v hb
def cl_2741 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,true),(59,true)]
theorem inp_2741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2741 v hb
def cl_2742 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,true),(59,true)]
theorem inp_2742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2742 (by decide) v hb
def cl_2743 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,true),(59,true)]
theorem inp_2743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2743 v hb
def cl_2744 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,false),(52,true),(59,true)]
theorem inp_2744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2744 (by decide) v hb
def cl_2745 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,true),(59,true)]
theorem inp_2745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2745 (by decide) v hb
def cl_2746 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,true),(59,true)]
theorem inp_2746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2746 (by decide) v hb
end Percolation.NReplay
