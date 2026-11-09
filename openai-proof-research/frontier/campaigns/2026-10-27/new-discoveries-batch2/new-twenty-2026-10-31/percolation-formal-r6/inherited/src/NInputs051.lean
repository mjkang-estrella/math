import NInputs050
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3155 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,true),(60,false)]
theorem inp_3155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3155 (by decide) v hb
def cl_3156 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,true),(60,false)]
theorem inp_3156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3156 v hb
def cl_3157 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,true),(60,false)]
theorem inp_3157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3157 (by decide) v hb
def cl_3158 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,true),(60,false)]
theorem inp_3158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3158 (by decide) v hb
def cl_3159 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,true),(60,false)]
theorem inp_3159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3159 v hb
def cl_3160 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,true),(60,false)]
theorem inp_3160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3160 (by decide) v hb
def cl_3161 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,true),(60,false)]
theorem inp_3161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3161 (by decide) v hb
def cl_3162 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,true),(60,false)]
theorem inp_3162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3162 (by decide) v hb
def cl_3163 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,true),(60,false)]
theorem inp_3163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3163 (by decide) v hb
def cl_3164 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,true),(60,false)]
theorem inp_3164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3164 v hb
def cl_3165 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,true),(60,false)]
theorem inp_3165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3165 (by decide) v hb
def cl_3166 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,true),(55,true),(60,false)]
theorem inp_3166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3166 (by decide) v hb
def cl_3167 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,true),(60,false)]
theorem inp_3167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3167 v hb
def cl_3168 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,true),(55,true),(60,false)]
theorem inp_3168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3168 (by decide) v hb
def cl_3169 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,false),(60,true)]
theorem inp_3169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3169 (by decide) v hb
def cl_3170 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,false),(60,true)]
theorem inp_3170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3170 (by decide) v hb
def cl_3171 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,false),(60,true)]
theorem inp_3171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3171 v hb
def cl_3172 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,false),(60,true)]
theorem inp_3172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3172 v hb
def cl_3173 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,false),(60,true)]
theorem inp_3173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3173 (by decide) v hb
def cl_3174 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,false),(60,true)]
theorem inp_3174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3174 (by decide) v hb
def cl_3175 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,false),(60,true)]
theorem inp_3175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3175 v hb
def cl_3176 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,false),(60,true)]
theorem inp_3176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3176 v hb
def cl_3177 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,false),(60,true)]
theorem inp_3177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3177 (by decide) v hb
def cl_3178 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,false),(60,true)]
theorem inp_3178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3178 (by decide) v hb
def cl_3179 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,false),(60,true)]
theorem inp_3179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3179 v hb
def cl_3180 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,false),(60,true)]
theorem inp_3180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3180 v hb
def cl_3181 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,false),(60,true)]
theorem inp_3181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3181 (by decide) v hb
def cl_3182 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,true),(55,false),(60,true)]
theorem inp_3182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3182 (by decide) v hb
def cl_3183 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,false),(60,true)]
theorem inp_3183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3183 v hb
def cl_3184 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,true),(55,false),(60,true)]
theorem inp_3184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3184 (by decide) v hb
def cl_3185 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,true),(60,true)]
theorem inp_3185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3185 (by decide) v hb
def cl_3186 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,true),(60,true)]
theorem inp_3186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3186 (by decide) v hb
def cl_3187 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,true),(60,true)]
theorem inp_3187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3187 (by decide) v hb
def cl_3188 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,true),(60,true)]
theorem inp_3188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3188 v hb
def cl_3189 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,true),(60,true)]
theorem inp_3189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3189 (by decide) v hb
def cl_3190 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,true),(60,true)]
theorem inp_3190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3190 (by decide) v hb
def cl_3191 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,true),(60,true)]
theorem inp_3191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3191 v hb
def cl_3192 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,false),(55,true),(60,true)]
theorem inp_3192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3192 (by decide) v hb
def cl_3193 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,true),(60,true)]
theorem inp_3193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3193 (by decide) v hb
def cl_3194 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,true),(60,true)]
theorem inp_3194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3194 (by decide) v hb
def cl_3195 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,true),(60,true)]
theorem inp_3195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3195 (by decide) v hb
def cl_3196 : CNF.NClause := [(111,false),(34,true),(38,true),(42,false),(46,true),(55,true),(60,true)]
theorem inp_3196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3196 (by decide) v hb
def cl_3197 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,true),(60,true)]
theorem inp_3197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3197 (by decide) v hb
def cl_3198 : CNF.NClause := [(111,false),(34,true),(38,false),(42,true),(46,true),(55,true),(60,true)]
theorem inp_3198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3198 (by decide) v hb
def cl_3199 : CNF.NClause := [(111,false),(34,false),(38,true),(42,true),(46,true),(55,true),(60,true)]
theorem inp_3199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3199 (by decide) v hb
def cl_3200 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,true),(55,true),(60,true)]
theorem inp_3200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3200 (by decide) v hb
def cl_3201 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3201 v hb
def cl_3202 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3202 v hb
def cl_3203 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3203 v hb
def cl_3204 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3204 v hb
end Percolation.NReplay
