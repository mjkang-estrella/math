import NInputs048
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3055 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,true),(53,false),(58,true)]
theorem inp_3055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3055 (by decide) v hb
def cl_3056 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,true),(53,false),(58,true)]
theorem inp_3056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3056 (by decide) v hb
def cl_3057 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,true),(58,true)]
theorem inp_3057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3057 (by decide) v hb
def cl_3058 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,true),(58,true)]
theorem inp_3058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3058 (by decide) v hb
def cl_3059 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,true),(58,true)]
theorem inp_3059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3059 v hb
def cl_3060 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,true),(58,true)]
theorem inp_3060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3060 v hb
def cl_3061 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,true),(58,true)]
theorem inp_3061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3061 (by decide) v hb
def cl_3062 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,true),(58,true)]
theorem inp_3062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3062 (by decide) v hb
def cl_3063 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,true),(58,true)]
theorem inp_3063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3063 v hb
def cl_3064 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,false),(53,true),(58,true)]
theorem inp_3064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3064 (by decide) v hb
def cl_3065 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,true),(58,true)]
theorem inp_3065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3065 (by decide) v hb
def cl_3066 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,true),(58,true)]
theorem inp_3066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3066 (by decide) v hb
def cl_3067 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,true),(58,true)]
theorem inp_3067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3067 v hb
def cl_3068 : CNF.NClause := [(109,false),(35,true),(37,true),(44,false),(46,true),(53,true),(58,true)]
theorem inp_3068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3068 (by decide) v hb
def cl_3069 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,true),(58,true)]
theorem inp_3069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3069 (by decide) v hb
def cl_3070 : CNF.NClause := [(109,false),(35,true),(37,false),(44,true),(46,true),(53,true),(58,true)]
theorem inp_3070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3070 (by decide) v hb
def cl_3071 : CNF.NClause := [(109,false),(35,false),(37,true),(44,true),(46,true),(53,true),(58,true)]
theorem inp_3071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3071 (by decide) v hb
def cl_3072 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,true),(53,true),(58,true)]
theorem inp_3072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3072 (by decide) v hb
def cl_3073 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,false),(57,false)]
theorem inp_3073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3073 v hb
def cl_3074 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,false),(57,false)]
theorem inp_3074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3074 v hb
def cl_3075 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,false),(57,false)]
theorem inp_3075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3075 (by decide) v hb
def cl_3076 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,false),(57,false)]
theorem inp_3076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3076 (by decide) v hb
def cl_3077 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,false),(57,false)]
theorem inp_3077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3077 (by decide) v hb
def cl_3078 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,false),(57,false)]
theorem inp_3078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3078 (by decide) v hb
def cl_3079 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,false),(57,false)]
theorem inp_3079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3079 (by decide) v hb
def cl_3080 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,false),(52,false),(57,false)]
theorem inp_3080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3080 (by decide) v hb
def cl_3081 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,false),(57,false)]
theorem inp_3081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3081 (by decide) v hb
def cl_3082 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,false),(57,false)]
theorem inp_3082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3082 v hb
def cl_3083 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,false),(57,false)]
theorem inp_3083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3083 (by decide) v hb
def cl_3084 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,true),(52,false),(57,false)]
theorem inp_3084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3084 (by decide) v hb
def cl_3085 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,false),(57,false)]
theorem inp_3085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3085 (by decide) v hb
def cl_3086 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,true),(52,false),(57,false)]
theorem inp_3086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3086 (by decide) v hb
def cl_3087 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,true),(52,false),(57,false)]
theorem inp_3087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3087 (by decide) v hb
def cl_3088 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,true),(52,false),(57,false)]
theorem inp_3088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3088 (by decide) v hb
def cl_3089 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,true),(57,false)]
theorem inp_3089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3089 (by decide) v hb
def cl_3090 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,true),(57,false)]
theorem inp_3090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3090 (by decide) v hb
def cl_3091 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,true),(57,false)]
theorem inp_3091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3091 (by decide) v hb
def cl_3092 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,true),(57,false)]
theorem inp_3092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3092 (by decide) v hb
def cl_3093 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,true),(57,false)]
theorem inp_3093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3093 (by decide) v hb
def cl_3094 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,true),(57,false)]
theorem inp_3094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3094 (by decide) v hb
def cl_3095 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,true),(57,false)]
theorem inp_3095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3095 (by decide) v hb
def cl_3096 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,false),(52,true),(57,false)]
theorem inp_3096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3096 (by decide) v hb
def cl_3097 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,true),(57,false)]
theorem inp_3097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3097 (by decide) v hb
def cl_3098 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,true),(57,false)]
theorem inp_3098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3098 v hb
def cl_3099 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,true),(57,false)]
theorem inp_3099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3099 (by decide) v hb
def cl_3100 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,true),(52,true),(57,false)]
theorem inp_3100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3100 (by decide) v hb
def cl_3101 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,true),(57,false)]
theorem inp_3101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3101 (by decide) v hb
def cl_3102 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,true),(52,true),(57,false)]
theorem inp_3102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3102 (by decide) v hb
def cl_3103 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,true),(52,true),(57,false)]
theorem inp_3103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3103 (by decide) v hb
def cl_3104 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,true),(52,true),(57,false)]
theorem inp_3104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3104 (by decide) v hb
end Percolation.NReplay
