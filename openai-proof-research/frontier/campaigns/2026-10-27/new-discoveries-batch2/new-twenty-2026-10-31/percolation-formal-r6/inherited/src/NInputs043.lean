import NInputs042
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2747 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,true),(59,true)]
theorem inp_2747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2747 (by decide) v hb
def cl_2748 : CNF.NClause := [(104,false),(35,true),(38,true),(41,false),(49,true),(52,true),(59,true)]
theorem inp_2748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2748 (by decide) v hb
def cl_2749 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,true),(59,true)]
theorem inp_2749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2749 (by decide) v hb
def cl_2750 : CNF.NClause := [(104,false),(35,true),(38,false),(41,true),(49,true),(52,true),(59,true)]
theorem inp_2750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2750 (by decide) v hb
def cl_2751 : CNF.NClause := [(104,false),(35,false),(38,true),(41,true),(49,true),(52,true),(59,true)]
theorem inp_2751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2751 (by decide) v hb
def cl_2752 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,true),(52,true),(59,true)]
theorem inp_2752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2752 (by decide) v hb
def cl_2753 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,false),(60,false)]
theorem inp_2753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2753 v hb
def cl_2754 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,false),(60,false)]
theorem inp_2754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2754 (by decide) v hb
def cl_2755 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,false),(60,false)]
theorem inp_2755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2755 v hb
def cl_2756 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,false),(60,false)]
theorem inp_2756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2756 (by decide) v hb
def cl_2757 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,false),(60,false)]
theorem inp_2757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2757 (by decide) v hb
def cl_2758 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,false),(60,false)]
theorem inp_2758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2758 (by decide) v hb
def cl_2759 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,false),(60,false)]
theorem inp_2759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2759 (by decide) v hb
def cl_2760 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,false),(54,false),(60,false)]
theorem inp_2760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2760 (by decide) v hb
def cl_2761 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,false),(60,false)]
theorem inp_2761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2761 (by decide) v hb
def cl_2762 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,false),(60,false)]
theorem inp_2762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2762 (by decide) v hb
def cl_2763 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,false),(60,false)]
theorem inp_2763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2763 (by decide) v hb
def cl_2764 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,true),(54,false),(60,false)]
theorem inp_2764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2764 (by decide) v hb
def cl_2765 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,false),(60,false)]
theorem inp_2765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2765 (by decide) v hb
def cl_2766 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,true),(54,false),(60,false)]
theorem inp_2766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2766 (by decide) v hb
def cl_2767 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,false),(60,false)]
theorem inp_2767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2767 v hb
def cl_2768 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,true),(54,false),(60,false)]
theorem inp_2768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2768 (by decide) v hb
def cl_2769 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,true),(60,false)]
theorem inp_2769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2769 (by decide) v hb
def cl_2770 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,true),(60,false)]
theorem inp_2770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2770 (by decide) v hb
def cl_2771 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,true),(60,false)]
theorem inp_2771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2771 (by decide) v hb
def cl_2772 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,true),(60,false)]
theorem inp_2772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2772 (by decide) v hb
def cl_2773 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,true),(60,false)]
theorem inp_2773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2773 (by decide) v hb
def cl_2774 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,true),(60,false)]
theorem inp_2774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2774 (by decide) v hb
def cl_2775 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,true),(60,false)]
theorem inp_2775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2775 (by decide) v hb
def cl_2776 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,false),(54,true),(60,false)]
theorem inp_2776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2776 (by decide) v hb
def cl_2777 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,true),(60,false)]
theorem inp_2777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2777 (by decide) v hb
def cl_2778 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,true),(60,false)]
theorem inp_2778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2778 (by decide) v hb
def cl_2779 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,true),(60,false)]
theorem inp_2779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2779 (by decide) v hb
def cl_2780 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,true),(54,true),(60,false)]
theorem inp_2780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2780 (by decide) v hb
def cl_2781 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,true),(60,false)]
theorem inp_2781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2781 (by decide) v hb
def cl_2782 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,true),(54,true),(60,false)]
theorem inp_2782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2782 (by decide) v hb
def cl_2783 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,true),(60,false)]
theorem inp_2783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2783 (by decide) v hb
def cl_2784 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,true),(54,true),(60,false)]
theorem inp_2784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2784 (by decide) v hb
def cl_2785 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,false),(60,true)]
theorem inp_2785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2785 (by decide) v hb
def cl_2786 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,false),(60,true)]
theorem inp_2786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2786 (by decide) v hb
def cl_2787 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,false),(60,true)]
theorem inp_2787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2787 (by decide) v hb
def cl_2788 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,false),(60,true)]
theorem inp_2788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2788 (by decide) v hb
def cl_2789 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,false),(60,true)]
theorem inp_2789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2789 (by decide) v hb
def cl_2790 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,false),(60,true)]
theorem inp_2790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2790 (by decide) v hb
def cl_2791 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,false),(60,true)]
theorem inp_2791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2791 (by decide) v hb
def cl_2792 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,false),(54,false),(60,true)]
theorem inp_2792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2792 (by decide) v hb
def cl_2793 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,false),(60,true)]
theorem inp_2793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2793 (by decide) v hb
def cl_2794 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,false),(60,true)]
theorem inp_2794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2794 (by decide) v hb
def cl_2795 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,false),(60,true)]
theorem inp_2795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2795 (by decide) v hb
def cl_2796 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,true),(54,false),(60,true)]
theorem inp_2796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2796 (by decide) v hb
end Percolation.NReplay
