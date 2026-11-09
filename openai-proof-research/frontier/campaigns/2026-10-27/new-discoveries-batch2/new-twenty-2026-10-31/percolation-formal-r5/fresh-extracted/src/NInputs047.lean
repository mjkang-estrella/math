import NInputs046
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2950 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,false),(61,false)]
theorem inp_2950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2950 (by decide) v hb
def cl_2951 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,false),(61,false)]
theorem inp_2951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2951 (by decide) v hb
def cl_2952 : CNF.NClause := [(108,true),(46,true),(47,true),(48,true),(49,false),(50,false),(61,false)]
theorem inp_2952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2952 (by decide) v hb
def cl_2953 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,false),(61,false)]
theorem inp_2953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2953 (by decide) v hb
def cl_2954 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,false),(61,false)]
theorem inp_2954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2954 (by decide) v hb
def cl_2955 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,false),(61,false)]
theorem inp_2955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2955 (by decide) v hb
def cl_2957 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,false),(61,false)]
theorem inp_2957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2957 (by decide) v hb
def cl_2958 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,true),(50,false),(61,false)]
theorem inp_2958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2958 (by decide) v hb
def cl_2959 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,true),(50,false),(61,false)]
theorem inp_2959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2959 (by decide) v hb
def cl_2960 : CNF.NClause := [(108,true),(46,true),(47,true),(48,true),(49,true),(50,false),(61,false)]
theorem inp_2960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2960 (by decide) v hb
def cl_2961 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,true),(61,false)]
theorem inp_2961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2961 (by decide) v hb
def cl_2962 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,true),(61,false)]
theorem inp_2962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2962 (by decide) v hb
def cl_2963 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,true),(61,false)]
theorem inp_2963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2963 (by decide) v hb
def cl_2964 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,true),(61,false)]
theorem inp_2964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2964 (by decide) v hb
def cl_2966 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,true),(61,false)]
theorem inp_2966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2966 (by decide) v hb
def cl_2967 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,true),(61,false)]
theorem inp_2967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2967 (by decide) v hb
def cl_2969 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,true),(61,false)]
theorem inp_2969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2969 (by decide) v hb
def cl_2970 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,true),(61,false)]
theorem inp_2970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2970 (by decide) v hb
def cl_2971 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,true),(61,false)]
theorem inp_2971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2971 (by decide) v hb
def cl_2973 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,true),(61,false)]
theorem inp_2973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2973 (by decide) v hb
def cl_2974 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,true),(50,true),(61,false)]
theorem inp_2974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2974 (by decide) v hb
def cl_2975 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,true),(50,true),(61,false)]
theorem inp_2975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2975 (by decide) v hb
def cl_2977 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,false),(61,true)]
theorem inp_2977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2977 (by decide) v hb
def cl_2978 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,false),(61,true)]
theorem inp_2978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2978 (by decide) v hb
def cl_2979 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,false),(61,true)]
theorem inp_2979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2979 v hb
def cl_2980 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,false),(61,true)]
theorem inp_2980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2980 v hb
def cl_2981 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,false),(50,false),(61,true)]
theorem inp_2981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2981 (by decide) v hb
def cl_2982 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,false),(61,true)]
theorem inp_2982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2982 (by decide) v hb
def cl_2983 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,false),(61,true)]
theorem inp_2983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2983 v hb
def cl_2984 : CNF.NClause := [(108,true),(46,true),(47,true),(48,true),(49,false),(50,false),(61,true)]
theorem inp_2984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2984 v hb
def cl_2985 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,false),(61,true)]
theorem inp_2985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2985 (by decide) v hb
def cl_2986 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,false),(61,true)]
theorem inp_2986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2986 (by decide) v hb
def cl_2987 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,false),(61,true)]
theorem inp_2987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2987 v hb
def cl_2988 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,true),(50,false),(61,true)]
theorem inp_2988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2988 (by decide) v hb
def cl_2989 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,false),(61,true)]
theorem inp_2989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2989 (by decide) v hb
def cl_2990 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,true),(50,false),(61,true)]
theorem inp_2990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2990 (by decide) v hb
def cl_2991 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,true),(50,false),(61,true)]
theorem inp_2991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2991 v hb
def cl_2992 : CNF.NClause := [(108,false),(46,true),(47,true),(48,true),(49,true),(50,false),(61,true)]
theorem inp_2992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2992 (by decide) v hb
def cl_2993 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,true),(61,true)]
theorem inp_2993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2993 (by decide) v hb
def cl_2994 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,true),(61,true)]
theorem inp_2994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2994 (by decide) v hb
def cl_2995 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,true),(61,true)]
theorem inp_2995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2995 v hb
def cl_2996 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,true),(61,true)]
theorem inp_2996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2996 v hb
def cl_2997 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,false),(50,true),(61,true)]
theorem inp_2997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2997 (by decide) v hb
def cl_2998 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,true),(61,true)]
theorem inp_2998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2998 (by decide) v hb
def cl_2999 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,true),(61,true)]
theorem inp_2999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2999 v hb
def cl_3000 : CNF.NClause := [(108,false),(46,true),(47,true),(48,true),(49,false),(50,true),(61,true)]
theorem inp_3000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3000 (by decide) v hb
def cl_3001 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,true),(61,true)]
theorem inp_3001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3001 (by decide) v hb
def cl_3002 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,true),(61,true)]
theorem inp_3002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3002 (by decide) v hb
def cl_3003 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,true),(61,true)]
theorem inp_3003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3003 (by decide) v hb
def cl_3004 : CNF.NClause := [(108,false),(46,true),(47,true),(48,false),(49,true),(50,true),(61,true)]
theorem inp_3004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3004 (by decide) v hb
end Percolation.NReplay
