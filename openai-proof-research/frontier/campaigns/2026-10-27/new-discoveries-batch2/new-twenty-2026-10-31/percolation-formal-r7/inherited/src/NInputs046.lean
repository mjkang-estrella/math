import NInputs045
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2897 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,true),(58,false)]
theorem inp_2897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2897 (by decide) v hb
def cl_2898 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,true),(58,false)]
theorem inp_2898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2898 (by decide) v hb
def cl_2899 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,true),(58,false)]
theorem inp_2899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2899 (by decide) v hb
def cl_2900 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,true),(58,false)]
theorem inp_2900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2900 (by decide) v hb
def cl_2901 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,true),(58,false)]
theorem inp_2901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2901 (by decide) v hb
def cl_2902 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,true),(58,false)]
theorem inp_2902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2902 (by decide) v hb
def cl_2903 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,true),(58,false)]
theorem inp_2903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2903 v hb
def cl_2904 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,false),(55,true),(58,false)]
theorem inp_2904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2904 (by decide) v hb
def cl_2905 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,true),(58,false)]
theorem inp_2905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2905 (by decide) v hb
def cl_2906 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,true),(58,false)]
theorem inp_2906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2906 (by decide) v hb
def cl_2907 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,true),(58,false)]
theorem inp_2907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2907 (by decide) v hb
def cl_2908 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,true),(55,true),(58,false)]
theorem inp_2908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2908 (by decide) v hb
def cl_2909 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,true),(58,false)]
theorem inp_2909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2909 (by decide) v hb
def cl_2910 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,true),(55,true),(58,false)]
theorem inp_2910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2910 (by decide) v hb
def cl_2911 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(55,true),(58,false)]
theorem inp_2911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2911 (by decide) v hb
def cl_2912 : CNF.NClause := [(107,false),(32,true),(39,true),(41,true),(48,true),(55,true),(58,false)]
theorem inp_2912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2912 (by decide) v hb
def cl_2913 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,false),(58,true)]
theorem inp_2913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2913 (by decide) v hb
def cl_2914 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,false),(58,true)]
theorem inp_2914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2914 (by decide) v hb
def cl_2915 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,false),(58,true)]
theorem inp_2915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2915 (by decide) v hb
def cl_2916 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,false),(58,true)]
theorem inp_2916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2916 (by decide) v hb
def cl_2917 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,false),(58,true)]
theorem inp_2917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2917 (by decide) v hb
def cl_2918 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,false),(58,true)]
theorem inp_2918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2918 (by decide) v hb
def cl_2919 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,false),(58,true)]
theorem inp_2919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2919 v hb
def cl_2920 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,false),(55,false),(58,true)]
theorem inp_2920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2920 v hb
def cl_2921 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,false),(58,true)]
theorem inp_2921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2921 (by decide) v hb
def cl_2922 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,false),(58,true)]
theorem inp_2922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2922 (by decide) v hb
def cl_2923 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,false),(58,true)]
theorem inp_2923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2923 (by decide) v hb
def cl_2924 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,true),(55,false),(58,true)]
theorem inp_2924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2924 (by decide) v hb
def cl_2925 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,false),(58,true)]
theorem inp_2925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2925 (by decide) v hb
def cl_2926 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,true),(55,false),(58,true)]
theorem inp_2926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2926 (by decide) v hb
def cl_2927 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(55,false),(58,true)]
theorem inp_2927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2927 (by decide) v hb
def cl_2929 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,true),(58,true)]
theorem inp_2929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2929 (by decide) v hb
def cl_2930 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,true),(58,true)]
theorem inp_2930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2930 (by decide) v hb
def cl_2931 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,true),(58,true)]
theorem inp_2931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2931 (by decide) v hb
def cl_2932 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,true),(58,true)]
theorem inp_2932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2932 (by decide) v hb
def cl_2933 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,true),(58,true)]
theorem inp_2933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2933 (by decide) v hb
def cl_2934 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,true),(58,true)]
theorem inp_2934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2934 (by decide) v hb
def cl_2935 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,true),(58,true)]
theorem inp_2935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2935 v hb
def cl_2936 : CNF.NClause := [(107,false),(32,true),(39,true),(41,true),(48,false),(55,true),(58,true)]
theorem inp_2936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2936 (by decide) v hb
def cl_2937 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,true),(58,true)]
theorem inp_2937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2937 (by decide) v hb
def cl_2938 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,true),(58,true)]
theorem inp_2938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2938 (by decide) v hb
def cl_2939 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,true),(58,true)]
theorem inp_2939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2939 (by decide) v hb
def cl_2941 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,true),(58,true)]
theorem inp_2941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2941 (by decide) v hb
def cl_2942 : CNF.NClause := [(107,false),(32,true),(39,false),(41,true),(48,true),(55,true),(58,true)]
theorem inp_2942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2942 (by decide) v hb
def cl_2943 : CNF.NClause := [(107,false),(32,false),(39,true),(41,true),(48,true),(55,true),(58,true)]
theorem inp_2943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2943 (by decide) v hb
def cl_2944 : CNF.NClause := [(107,false),(32,true),(39,true),(41,true),(48,true),(55,true),(58,true)]
theorem inp_2944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2944 (by decide) v hb
def cl_2945 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,false),(61,false)]
theorem inp_2945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2945 v hb
def cl_2946 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,false),(61,false)]
theorem inp_2946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2946 v hb
def cl_2947 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,false),(61,false)]
theorem inp_2947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2947 (by decide) v hb
def cl_2948 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,false),(61,false)]
theorem inp_2948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2948 (by decide) v hb
end Percolation.NReplay
