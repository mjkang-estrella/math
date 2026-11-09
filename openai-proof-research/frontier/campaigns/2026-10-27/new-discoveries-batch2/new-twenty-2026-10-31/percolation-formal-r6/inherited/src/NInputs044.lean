import NInputs043
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2797 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,false),(60,true)]
theorem inp_2797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2797 (by decide) v hb
def cl_2798 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,true),(54,false),(60,true)]
theorem inp_2798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2798 (by decide) v hb
def cl_2799 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,false),(60,true)]
theorem inp_2799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2799 v hb
def cl_2800 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,true),(54,false),(60,true)]
theorem inp_2800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2800 (by decide) v hb
def cl_2801 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,true),(60,true)]
theorem inp_2801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2801 (by decide) v hb
def cl_2802 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,true),(60,true)]
theorem inp_2802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2802 (by decide) v hb
def cl_2803 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,true),(60,true)]
theorem inp_2803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2803 (by decide) v hb
def cl_2804 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,true),(60,true)]
theorem inp_2804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2804 (by decide) v hb
def cl_2805 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,true),(60,true)]
theorem inp_2805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2805 (by decide) v hb
def cl_2806 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,true),(60,true)]
theorem inp_2806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2806 (by decide) v hb
def cl_2807 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,true),(60,true)]
theorem inp_2807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2807 (by decide) v hb
def cl_2808 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,false),(54,true),(60,true)]
theorem inp_2808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2808 (by decide) v hb
def cl_2809 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,true),(60,true)]
theorem inp_2809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2809 (by decide) v hb
def cl_2810 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,true),(60,true)]
theorem inp_2810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2810 (by decide) v hb
def cl_2811 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,true),(60,true)]
theorem inp_2811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2811 (by decide) v hb
def cl_2812 : CNF.NClause := [(105,false),(33,true),(37,true),(41,false),(50,true),(54,true),(60,true)]
theorem inp_2812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2812 (by decide) v hb
def cl_2813 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,true),(60,true)]
theorem inp_2813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2813 (by decide) v hb
def cl_2814 : CNF.NClause := [(105,false),(33,true),(37,false),(41,true),(50,true),(54,true),(60,true)]
theorem inp_2814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2814 (by decide) v hb
def cl_2815 : CNF.NClause := [(105,false),(33,false),(37,true),(41,true),(50,true),(54,true),(60,true)]
theorem inp_2815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2815 (by decide) v hb
def cl_2816 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,true),(54,true),(60,true)]
theorem inp_2816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2816 (by decide) v hb
def cl_2817 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,false),(57,false)]
theorem inp_2817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2817 v hb
def cl_2818 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,false),(57,false)]
theorem inp_2818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2818 v hb
def cl_2819 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,false),(57,false)]
theorem inp_2819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2819 v hb
def cl_2820 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,false),(57,false)]
theorem inp_2820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2820 (by decide) v hb
def cl_2821 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,false),(57,false)]
theorem inp_2821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2821 v hb
def cl_2822 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,false),(57,false)]
theorem inp_2822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2822 (by decide) v hb
def cl_2823 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,false),(57,false)]
theorem inp_2823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2823 v hb
def cl_2824 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,false),(53,false),(57,false)]
theorem inp_2824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2824 (by decide) v hb
def cl_2825 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,false),(57,false)]
theorem inp_2825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2825 (by decide) v hb
def cl_2826 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,false),(57,false)]
theorem inp_2826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2826 v hb
def cl_2827 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,false),(57,false)]
theorem inp_2827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2827 (by decide) v hb
def cl_2828 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,true),(53,false),(57,false)]
theorem inp_2828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2828 (by decide) v hb
def cl_2829 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,false),(57,false)]
theorem inp_2829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2829 v hb
def cl_2830 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,false),(57,false)]
theorem inp_2830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2830 v hb
def cl_2831 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,true),(53,false),(57,false)]
theorem inp_2831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2831 (by decide) v hb
def cl_2832 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,true),(53,false),(57,false)]
theorem inp_2832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2832 (by decide) v hb
def cl_2833 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,true),(57,false)]
theorem inp_2833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2833 (by decide) v hb
def cl_2834 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,true),(57,false)]
theorem inp_2834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2834 (by decide) v hb
def cl_2835 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,true),(57,false)]
theorem inp_2835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2835 (by decide) v hb
def cl_2836 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,true),(57,false)]
theorem inp_2836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2836 (by decide) v hb
def cl_2837 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,true),(57,false)]
theorem inp_2837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2837 (by decide) v hb
def cl_2838 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,true),(57,false)]
theorem inp_2838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2838 (by decide) v hb
def cl_2839 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,true),(57,false)]
theorem inp_2839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2839 (by decide) v hb
def cl_2840 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,false),(53,true),(57,false)]
theorem inp_2840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2840 (by decide) v hb
def cl_2841 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,true),(57,false)]
theorem inp_2841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2841 (by decide) v hb
def cl_2842 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,true),(57,false)]
theorem inp_2842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2842 v hb
def cl_2843 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,true),(57,false)]
theorem inp_2843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2843 (by decide) v hb
def cl_2844 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,true),(53,true),(57,false)]
theorem inp_2844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2844 (by decide) v hb
def cl_2845 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,true),(57,false)]
theorem inp_2845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2845 v hb
def cl_2846 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,true),(57,false)]
theorem inp_2846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2846 v hb
end Percolation.NReplay
