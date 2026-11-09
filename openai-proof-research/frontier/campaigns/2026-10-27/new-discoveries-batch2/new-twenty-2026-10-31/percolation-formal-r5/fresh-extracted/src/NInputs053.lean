import NInputs052
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3255 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,true),(59,true)]
theorem inp_3255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3255 v hb
def cl_3256 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,false),(54,true),(59,true)]
theorem inp_3256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3256 (by decide) v hb
def cl_3257 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,true),(59,true)]
theorem inp_3257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3257 v hb
def cl_3258 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,true),(59,true)]
theorem inp_3258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3258 (by decide) v hb
def cl_3259 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,true),(59,true)]
theorem inp_3259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3259 v hb
def cl_3260 : CNF.NClause := [(112,false),(32,true),(40,true),(43,false),(46,true),(54,true),(59,true)]
theorem inp_3260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3260 (by decide) v hb
def cl_3261 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,true),(59,true)]
theorem inp_3261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3261 (by decide) v hb
def cl_3262 : CNF.NClause := [(112,false),(32,true),(40,false),(43,true),(46,true),(54,true),(59,true)]
theorem inp_3262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3262 (by decide) v hb
def cl_3263 : CNF.NClause := [(112,false),(32,false),(40,true),(43,true),(46,true),(54,true),(59,true)]
theorem inp_3263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3263 (by decide) v hb
def cl_3264 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,true),(54,true),(59,true)]
theorem inp_3264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3264 (by decide) v hb
def cl_3265 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3265 v hb
def cl_3266 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3266 v hb
def cl_3267 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3267 v hb
def cl_3268 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3268 v hb
def cl_3269 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,false),(61,false)]
theorem inp_3269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3269 v hb
def cl_3270 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,false),(61,false)]
theorem inp_3270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3270 v hb
def cl_3271 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,false),(61,false)]
theorem inp_3271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3271 v hb
def cl_3272 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,false),(61,false)]
theorem inp_3272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3272 (by decide) v hb
def cl_3273 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,false),(61,false)]
theorem inp_3273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3273 v hb
def cl_3274 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,false),(61,false)]
theorem inp_3274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3274 v hb
def cl_3275 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,false),(61,false)]
theorem inp_3275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3275 v hb
def cl_3276 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,true),(40,false),(61,false)]
theorem inp_3276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3276 (by decide) v hb
def cl_3277 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,false),(61,false)]
theorem inp_3277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3277 v hb
def cl_3278 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,true),(40,false),(61,false)]
theorem inp_3278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3278 v hb
def cl_3279 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,true),(40,false),(61,false)]
theorem inp_3279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3279 v hb
def cl_3281 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,true),(61,false)]
theorem inp_3281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3281 (by decide) v hb
def cl_3282 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,true),(61,false)]
theorem inp_3282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3282 (by decide) v hb
def cl_3283 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,true),(61,false)]
theorem inp_3283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3283 v hb
def cl_3284 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,true),(61,false)]
theorem inp_3284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3284 (by decide) v hb
def cl_3285 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3285 v hb
def cl_3286 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3286 v hb
def cl_3287 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3287 v hb
def cl_3288 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3288 v hb
def cl_3289 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,true),(61,false)]
theorem inp_3289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3289 v hb
def cl_3291 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,true),(61,false)]
theorem inp_3291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3291 (by decide) v hb
def cl_3293 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,true),(61,false)]
theorem inp_3293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3293 v hb
def cl_3296 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,true),(40,true),(61,false)]
theorem inp_3296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3296 (by decide) v hb
def cl_3297 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,false),(61,true)]
theorem inp_3297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3297 (by decide) v hb
def cl_3298 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,false),(61,true)]
theorem inp_3298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3298 v hb
def cl_3299 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,false),(61,true)]
theorem inp_3299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3299 (by decide) v hb
def cl_3300 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,false),(61,true)]
theorem inp_3300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3300 (by decide) v hb
def cl_3301 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,false),(61,true)]
theorem inp_3301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3301 (by decide) v hb
def cl_3302 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,false),(61,true)]
theorem inp_3302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3302 v hb
def cl_3303 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,false),(61,true)]
theorem inp_3303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3303 (by decide) v hb
def cl_3304 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,false),(61,true)]
theorem inp_3304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3304 v hb
def cl_3305 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,false),(61,true)]
theorem inp_3305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3305 (by decide) v hb
def cl_3306 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,false),(61,true)]
theorem inp_3306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3306 (by decide) v hb
def cl_3307 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,false),(61,true)]
theorem inp_3307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3307 v hb
def cl_3308 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,true),(40,false),(61,true)]
theorem inp_3308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3308 (by decide) v hb
def cl_3309 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,false),(61,true)]
theorem inp_3309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3309 v hb
end Percolation.NReplay
