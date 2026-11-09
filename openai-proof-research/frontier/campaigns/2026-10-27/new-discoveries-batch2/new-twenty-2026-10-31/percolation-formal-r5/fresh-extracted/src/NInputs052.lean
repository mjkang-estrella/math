import NInputs051
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3205 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3205 v hb
def cl_3206 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3206 v hb
def cl_3207 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3207 v hb
def cl_3208 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3208 v hb
def cl_3209 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,false),(59,false)]
theorem inp_3209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3209 v hb
def cl_3210 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,false),(59,false)]
theorem inp_3210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3210 (by decide) v hb
def cl_3211 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,false),(59,false)]
theorem inp_3211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3211 v hb
def cl_3212 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,true),(54,false),(59,false)]
theorem inp_3212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3212 (by decide) v hb
def cl_3213 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,false),(59,false)]
theorem inp_3213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3213 v hb
def cl_3214 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,true),(54,false),(59,false)]
theorem inp_3214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3214 (by decide) v hb
def cl_3215 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,false),(59,false)]
theorem inp_3215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3215 v hb
def cl_3216 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,true),(54,false),(59,false)]
theorem inp_3216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3216 (by decide) v hb
def cl_3217 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,true),(59,false)]
theorem inp_3217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3217 v hb
def cl_3218 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,true),(59,false)]
theorem inp_3218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3218 v hb
def cl_3219 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,true),(59,false)]
theorem inp_3219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3219 (by decide) v hb
def cl_3220 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,true),(59,false)]
theorem inp_3220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3220 v hb
def cl_3221 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3221 v hb
def cl_3222 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3222 v hb
def cl_3223 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3223 v hb
def cl_3224 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3224 v hb
def cl_3225 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,true),(59,false)]
theorem inp_3225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3225 v hb
def cl_3226 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,true),(59,false)]
theorem inp_3226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3226 (by decide) v hb
def cl_3227 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,true),(59,false)]
theorem inp_3227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3227 v hb
def cl_3228 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,true),(54,true),(59,false)]
theorem inp_3228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3228 (by decide) v hb
def cl_3229 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,true),(59,false)]
theorem inp_3229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3229 (by decide) v hb
def cl_3230 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,true),(54,true),(59,false)]
theorem inp_3230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3230 (by decide) v hb
def cl_3231 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,true),(59,false)]
theorem inp_3231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3231 v hb
def cl_3232 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,true),(54,true),(59,false)]
theorem inp_3232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3232 (by decide) v hb
def cl_3233 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3233 v hb
def cl_3234 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3234 v hb
def cl_3235 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3235 v hb
def cl_3236 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3236 v hb
def cl_3237 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,false),(59,true)]
theorem inp_3237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3237 (by decide) v hb
def cl_3238 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,false),(59,true)]
theorem inp_3238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3238 (by decide) v hb
def cl_3239 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,false),(59,true)]
theorem inp_3239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3239 v hb
def cl_3240 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,false),(59,true)]
theorem inp_3240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3240 (by decide) v hb
def cl_3241 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,false),(59,true)]
theorem inp_3241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3241 v hb
def cl_3242 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,false),(59,true)]
theorem inp_3242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3242 (by decide) v hb
def cl_3243 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,false),(59,true)]
theorem inp_3243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3243 v hb
def cl_3244 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,true),(54,false),(59,true)]
theorem inp_3244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3244 (by decide) v hb
def cl_3245 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,false),(59,true)]
theorem inp_3245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3245 (by decide) v hb
def cl_3246 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,true),(54,false),(59,true)]
theorem inp_3246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3246 (by decide) v hb
def cl_3247 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,false),(59,true)]
theorem inp_3247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3247 v hb
def cl_3248 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,true),(54,false),(59,true)]
theorem inp_3248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3248 (by decide) v hb
def cl_3249 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,true),(59,true)]
theorem inp_3249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3249 (by decide) v hb
def cl_3250 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,true),(59,true)]
theorem inp_3250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3250 (by decide) v hb
def cl_3251 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,true),(59,true)]
theorem inp_3251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3251 (by decide) v hb
def cl_3252 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,true),(59,true)]
theorem inp_3252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3252 v hb
def cl_3253 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,true),(59,true)]
theorem inp_3253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3253 v hb
def cl_3254 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,true),(59,true)]
theorem inp_3254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3254 (by decide) v hb
end Percolation.NReplay
