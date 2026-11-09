import NInputs049
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3105 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,false),(57,true)]
theorem inp_3105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3105 (by decide) v hb
def cl_3106 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,false),(57,true)]
theorem inp_3106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3106 (by decide) v hb
def cl_3107 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,false),(57,true)]
theorem inp_3107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3107 (by decide) v hb
def cl_3108 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,false),(57,true)]
theorem inp_3108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3108 (by decide) v hb
def cl_3109 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,false),(57,true)]
theorem inp_3109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3109 (by decide) v hb
def cl_3110 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,false),(57,true)]
theorem inp_3110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3110 (by decide) v hb
def cl_3111 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,false),(57,true)]
theorem inp_3111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3111 (by decide) v hb
def cl_3112 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,false),(52,false),(57,true)]
theorem inp_3112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3112 (by decide) v hb
def cl_3113 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,false),(57,true)]
theorem inp_3113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3113 (by decide) v hb
def cl_3114 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,false),(57,true)]
theorem inp_3114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3114 v hb
def cl_3115 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,false),(57,true)]
theorem inp_3115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3115 (by decide) v hb
def cl_3116 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,true),(52,false),(57,true)]
theorem inp_3116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3116 (by decide) v hb
def cl_3117 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,false),(57,true)]
theorem inp_3117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3117 (by decide) v hb
def cl_3118 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,true),(52,false),(57,true)]
theorem inp_3118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3118 (by decide) v hb
def cl_3119 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,true),(52,false),(57,true)]
theorem inp_3119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3119 (by decide) v hb
def cl_3120 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,true),(52,false),(57,true)]
theorem inp_3120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3120 (by decide) v hb
def cl_3121 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,true),(57,true)]
theorem inp_3121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3121 v hb
def cl_3122 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,true),(57,true)]
theorem inp_3122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3122 (by decide) v hb
def cl_3123 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,true),(57,true)]
theorem inp_3123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3123 v hb
def cl_3124 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,true),(57,true)]
theorem inp_3124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3124 v hb
def cl_3125 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,true),(57,true)]
theorem inp_3125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3125 (by decide) v hb
def cl_3126 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,true),(57,true)]
theorem inp_3126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3126 (by decide) v hb
def cl_3127 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,true),(57,true)]
theorem inp_3127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3127 v hb
def cl_3128 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,false),(52,true),(57,true)]
theorem inp_3128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3128 (by decide) v hb
def cl_3129 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,true),(57,true)]
theorem inp_3129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3129 v hb
def cl_3130 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,true),(57,true)]
theorem inp_3130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3130 v hb
def cl_3131 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,true),(57,true)]
theorem inp_3131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3131 v hb
def cl_3132 : CNF.NClause := [(110,false),(33,true),(39,true),(45,false),(46,true),(52,true),(57,true)]
theorem inp_3132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3132 (by decide) v hb
def cl_3133 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,true),(57,true)]
theorem inp_3133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3133 (by decide) v hb
def cl_3134 : CNF.NClause := [(110,false),(33,true),(39,false),(45,true),(46,true),(52,true),(57,true)]
theorem inp_3134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3134 (by decide) v hb
def cl_3135 : CNF.NClause := [(110,false),(33,false),(39,true),(45,true),(46,true),(52,true),(57,true)]
theorem inp_3135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3135 (by decide) v hb
def cl_3136 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,true),(52,true),(57,true)]
theorem inp_3136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3136 (by decide) v hb
def cl_3137 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,false),(60,false)]
theorem inp_3137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3137 v hb
def cl_3138 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,false),(60,false)]
theorem inp_3138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3138 (by decide) v hb
def cl_3139 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,false),(60,false)]
theorem inp_3139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3139 v hb
def cl_3140 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,false),(60,false)]
theorem inp_3140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3140 v hb
def cl_3141 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,false),(60,false)]
theorem inp_3141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3141 (by decide) v hb
def cl_3142 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,false),(60,false)]
theorem inp_3142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3142 (by decide) v hb
def cl_3143 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,false),(60,false)]
theorem inp_3143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3143 v hb
def cl_3144 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,false),(60,false)]
theorem inp_3144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3144 v hb
def cl_3145 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,false),(60,false)]
theorem inp_3145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3145 (by decide) v hb
def cl_3146 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,false),(60,false)]
theorem inp_3146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3146 (by decide) v hb
def cl_3147 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,false),(60,false)]
theorem inp_3147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3147 (by decide) v hb
def cl_3148 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,false),(60,false)]
theorem inp_3148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3148 v hb
def cl_3149 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,false),(60,false)]
theorem inp_3149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3149 (by decide) v hb
def cl_3150 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,true),(55,false),(60,false)]
theorem inp_3150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3150 (by decide) v hb
def cl_3151 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,false),(60,false)]
theorem inp_3151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3151 v hb
def cl_3152 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,true),(55,false),(60,false)]
theorem inp_3152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3152 (by decide) v hb
def cl_3153 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,true),(60,false)]
theorem inp_3153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3153 (by decide) v hb
def cl_3154 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,true),(60,false)]
theorem inp_3154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3154 (by decide) v hb
end Percolation.NReplay
