import NInputs044
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2847 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,true),(53,true),(57,false)]
theorem inp_2847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2847 (by decide) v hb
def cl_2848 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,true),(53,true),(57,false)]
theorem inp_2848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2848 (by decide) v hb
def cl_2849 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,false),(57,true)]
theorem inp_2849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2849 (by decide) v hb
def cl_2850 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,false),(57,true)]
theorem inp_2850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2850 (by decide) v hb
def cl_2851 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,false),(57,true)]
theorem inp_2851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2851 (by decide) v hb
def cl_2852 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,false),(57,true)]
theorem inp_2852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2852 (by decide) v hb
def cl_2853 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,false),(57,true)]
theorem inp_2853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2853 (by decide) v hb
def cl_2854 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,false),(57,true)]
theorem inp_2854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2854 (by decide) v hb
def cl_2855 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,false),(57,true)]
theorem inp_2855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2855 v hb
def cl_2856 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,false),(53,false),(57,true)]
theorem inp_2856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2856 (by decide) v hb
def cl_2857 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,false),(57,true)]
theorem inp_2857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2857 (by decide) v hb
def cl_2858 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,false),(57,true)]
theorem inp_2858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2858 v hb
def cl_2859 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,false),(57,true)]
theorem inp_2859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2859 (by decide) v hb
def cl_2860 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,true),(53,false),(57,true)]
theorem inp_2860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2860 (by decide) v hb
def cl_2861 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,false),(57,true)]
theorem inp_2861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2861 v hb
def cl_2862 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,false),(57,true)]
theorem inp_2862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2862 v hb
def cl_2863 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,true),(53,false),(57,true)]
theorem inp_2863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2863 (by decide) v hb
def cl_2864 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,true),(53,false),(57,true)]
theorem inp_2864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2864 (by decide) v hb
def cl_2865 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,true),(57,true)]
theorem inp_2865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2865 (by decide) v hb
def cl_2866 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,true),(57,true)]
theorem inp_2866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2866 (by decide) v hb
def cl_2867 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,true),(57,true)]
theorem inp_2867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2867 (by decide) v hb
def cl_2868 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,true),(57,true)]
theorem inp_2868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2868 (by decide) v hb
def cl_2869 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,true),(57,true)]
theorem inp_2869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2869 (by decide) v hb
def cl_2870 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,true),(57,true)]
theorem inp_2870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2870 (by decide) v hb
def cl_2871 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,true),(57,true)]
theorem inp_2871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2871 v hb
def cl_2872 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,false),(53,true),(57,true)]
theorem inp_2872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2872 (by decide) v hb
def cl_2873 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,true),(57,true)]
theorem inp_2873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2873 (by decide) v hb
def cl_2874 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,true),(57,true)]
theorem inp_2874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2874 v hb
def cl_2875 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,true),(57,true)]
theorem inp_2875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2875 (by decide) v hb
def cl_2876 : CNF.NClause := [(106,false),(34,true),(40,true),(41,false),(47,true),(53,true),(57,true)]
theorem inp_2876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2876 (by decide) v hb
def cl_2877 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,true),(57,true)]
theorem inp_2877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2877 v hb
def cl_2878 : CNF.NClause := [(106,false),(34,true),(40,false),(41,true),(47,true),(53,true),(57,true)]
theorem inp_2878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2878 (by decide) v hb
def cl_2879 : CNF.NClause := [(106,false),(34,false),(40,true),(41,true),(47,true),(53,true),(57,true)]
theorem inp_2879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2879 (by decide) v hb
def cl_2880 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,true),(53,true),(57,true)]
theorem inp_2880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2880 (by decide) v hb
def cl_2881 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,false),(58,false)]
theorem inp_2881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2881 v hb
def cl_2882 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,false),(58,false)]
theorem inp_2882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2882 (by decide) v hb
def cl_2883 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,false),(58,false)]
theorem inp_2883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2883 (by decide) v hb
def cl_2884 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,false),(58,false)]
theorem inp_2884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2884 (by decide) v hb
def cl_2885 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,false),(58,false)]
theorem inp_2885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2885 v hb
def cl_2886 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,false),(58,false)]
theorem inp_2886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2886 (by decide) v hb
def cl_2887 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,false),(58,false)]
theorem inp_2887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2887 (by decide) v hb
def cl_2888 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,false),(55,false),(58,false)]
theorem inp_2888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2888 (by decide) v hb
def cl_2889 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,false),(58,false)]
theorem inp_2889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2889 (by decide) v hb
def cl_2890 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,false),(58,false)]
theorem inp_2890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2890 (by decide) v hb
def cl_2891 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,false),(58,false)]
theorem inp_2891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2891 (by decide) v hb
def cl_2892 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,true),(55,false),(58,false)]
theorem inp_2892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2892 (by decide) v hb
def cl_2893 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,false),(58,false)]
theorem inp_2893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2893 (by decide) v hb
def cl_2894 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,true),(55,false),(58,false)]
theorem inp_2894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2894 (by decide) v hb
def cl_2895 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(55,false),(58,false)]
theorem inp_2895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2895 (by decide) v hb
def cl_2896 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,true),(55,false),(58,false)]
theorem inp_2896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2896 (by decide) v hb
end Percolation.NReplay
