import NInputs053
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3310 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,true),(40,false),(61,true)]
theorem inp_3310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3310 v hb
def cl_3311 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,true),(40,false),(61,true)]
theorem inp_3311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3311 v hb
def cl_3312 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,true),(40,false),(61,true)]
theorem inp_3312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3312 (by decide) v hb
def cl_3313 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,true),(61,true)]
theorem inp_3313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3313 (by decide) v hb
def cl_3314 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,true),(61,true)]
theorem inp_3314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3314 v hb
def cl_3315 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,true),(61,true)]
theorem inp_3315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3315 (by decide) v hb
def cl_3316 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,true),(61,true)]
theorem inp_3316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3316 (by decide) v hb
def cl_3317 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,true),(61,true)]
theorem inp_3317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3317 v hb
def cl_3318 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,true),(61,true)]
theorem inp_3318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3318 v hb
def cl_3319 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,true),(61,true)]
theorem inp_3319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3319 (by decide) v hb
def cl_3320 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,false),(40,true),(61,true)]
theorem inp_3320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3320 (by decide) v hb
def cl_3321 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,true),(61,true)]
theorem inp_3321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3321 (by decide) v hb
def cl_3322 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,true),(61,true)]
theorem inp_3322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3322 (by decide) v hb
def cl_3323 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,true),(61,true)]
theorem inp_3323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3323 (by decide) v hb
def cl_3324 : CNF.NClause := [(113,false),(36,true),(37,true),(38,false),(39,true),(40,true),(61,true)]
theorem inp_3324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3324 (by decide) v hb
def cl_3325 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,true),(61,true)]
theorem inp_3325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3325 (by decide) v hb
def cl_3326 : CNF.NClause := [(113,false),(36,true),(37,false),(38,true),(39,true),(40,true),(61,true)]
theorem inp_3326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3326 (by decide) v hb
def cl_3327 : CNF.NClause := [(113,false),(36,false),(37,true),(38,true),(39,true),(40,true),(61,true)]
theorem inp_3327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3327 (by decide) v hb
def cl_3328 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,true),(40,true),(61,true)]
theorem inp_3328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3328 (by decide) v hb
def cl_3329 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,false),(57,false)]
theorem inp_3329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3329 (by decide) v hb
def cl_3330 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,false),(57,false)]
theorem inp_3330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3330 (by decide) v hb
def cl_3331 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,false),(57,false)]
theorem inp_3331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3331 v hb
def cl_3332 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,false),(57,false)]
theorem inp_3332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3332 v hb
def cl_3333 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,false),(57,false)]
theorem inp_3333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3333 (by decide) v hb
def cl_3334 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,false),(57,false)]
theorem inp_3334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3334 (by decide) v hb
def cl_3335 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,false),(57,false)]
theorem inp_3335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3335 v hb
def cl_3336 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,false),(57,false)]
theorem inp_3336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3336 v hb
def cl_3337 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,false),(57,false)]
theorem inp_3337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3337 (by decide) v hb
def cl_3338 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,false),(57,false)]
theorem inp_3338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3338 (by decide) v hb
def cl_3339 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,false),(57,false)]
theorem inp_3339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3339 (by decide) v hb
def cl_3340 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,false),(57,false)]
theorem inp_3340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3340 v hb
def cl_3341 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,false),(57,false)]
theorem inp_3341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3341 (by decide) v hb
def cl_3342 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,true),(54,false),(57,false)]
theorem inp_3342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3342 (by decide) v hb
def cl_3343 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,true),(54,false),(57,false)]
theorem inp_3343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3343 (by decide) v hb
def cl_3344 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,true),(54,false),(57,false)]
theorem inp_3344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3344 v hb
def cl_3345 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,true),(57,false)]
theorem inp_3345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3345 (by decide) v hb
def cl_3346 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,true),(57,false)]
theorem inp_3346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3346 (by decide) v hb
def cl_3347 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,true),(57,false)]
theorem inp_3347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3347 (by decide) v hb
def cl_3348 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,true),(57,false)]
theorem inp_3348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3348 v hb
def cl_3349 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,true),(57,false)]
theorem inp_3349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3349 (by decide) v hb
def cl_3350 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,true),(57,false)]
theorem inp_3350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3350 (by decide) v hb
def cl_3351 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,true),(57,false)]
theorem inp_3351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3351 (by decide) v hb
def cl_3352 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,true),(57,false)]
theorem inp_3352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3352 v hb
def cl_3353 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,true),(57,false)]
theorem inp_3353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3353 (by decide) v hb
def cl_3354 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,true),(57,false)]
theorem inp_3354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3354 (by decide) v hb
def cl_3355 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,true),(57,false)]
theorem inp_3355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3355 (by decide) v hb
def cl_3356 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,true),(57,false)]
theorem inp_3356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3356 v hb
def cl_3357 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,true),(57,false)]
theorem inp_3357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3357 (by decide) v hb
def cl_3358 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,true),(54,true),(57,false)]
theorem inp_3358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3358 (by decide) v hb
def cl_3359 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,true),(54,true),(57,false)]
theorem inp_3359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3359 (by decide) v hb
end Percolation.NReplay
