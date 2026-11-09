import NInputs054
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3360 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,true),(57,false)]
theorem inp_3360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3360 (by decide) v hb
def cl_3361 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,false),(57,true)]
theorem inp_3361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3361 (by decide) v hb
def cl_3362 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,false),(57,true)]
theorem inp_3362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3362 (by decide) v hb
def cl_3363 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,false),(57,true)]
theorem inp_3363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3363 (by decide) v hb
def cl_3364 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,false),(57,true)]
theorem inp_3364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3364 v hb
def cl_3365 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,false),(57,true)]
theorem inp_3365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3365 (by decide) v hb
def cl_3366 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,false),(57,true)]
theorem inp_3366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3366 (by decide) v hb
def cl_3367 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,false),(57,true)]
theorem inp_3367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3367 v hb
def cl_3368 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,false),(57,true)]
theorem inp_3368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3368 v hb
def cl_3369 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,false),(57,true)]
theorem inp_3369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3369 (by decide) v hb
def cl_3370 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,false),(57,true)]
theorem inp_3370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3370 (by decide) v hb
def cl_3371 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,false),(57,true)]
theorem inp_3371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3371 v hb
def cl_3372 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,false),(57,true)]
theorem inp_3372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3372 v hb
def cl_3373 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,false),(57,true)]
theorem inp_3373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3373 (by decide) v hb
def cl_3374 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,true),(54,false),(57,true)]
theorem inp_3374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3374 (by decide) v hb
def cl_3375 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,true),(54,false),(57,true)]
theorem inp_3375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3375 (by decide) v hb
def cl_3376 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,false),(57,true)]
theorem inp_3376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3376 (by decide) v hb
def cl_3377 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,true),(57,true)]
theorem inp_3377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3377 (by decide) v hb
def cl_3378 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,true),(57,true)]
theorem inp_3378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3378 (by decide) v hb
def cl_3379 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,true),(57,true)]
theorem inp_3379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3379 v hb
def cl_3380 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,true),(57,true)]
theorem inp_3380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3380 v hb
def cl_3381 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,true),(57,true)]
theorem inp_3381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3381 (by decide) v hb
def cl_3382 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,true),(57,true)]
theorem inp_3382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3382 (by decide) v hb
def cl_3383 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,true),(57,true)]
theorem inp_3383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3383 v hb
def cl_3384 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,false),(54,true),(57,true)]
theorem inp_3384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3384 (by decide) v hb
def cl_3385 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,true),(57,true)]
theorem inp_3385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3385 (by decide) v hb
def cl_3386 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,true),(57,true)]
theorem inp_3386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3386 (by decide) v hb
def cl_3387 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,true),(57,true)]
theorem inp_3387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3387 v hb
def cl_3388 : CNF.NClause := [(114,false),(35,true),(36,true),(42,false),(48,true),(54,true),(57,true)]
theorem inp_3388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3388 (by decide) v hb
def cl_3389 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,true),(57,true)]
theorem inp_3389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3389 (by decide) v hb
def cl_3390 : CNF.NClause := [(114,false),(35,true),(36,false),(42,true),(48,true),(54,true),(57,true)]
theorem inp_3390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3390 (by decide) v hb
def cl_3391 : CNF.NClause := [(114,false),(35,false),(36,true),(42,true),(48,true),(54,true),(57,true)]
theorem inp_3391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3391 v hb
def cl_3392 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,true),(57,true)]
theorem inp_3392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3392 v hb
def cl_3393 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,false),(59,false)]
theorem inp_3393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3393 (by decide) v hb
def cl_3394 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,false),(59,false)]
theorem inp_3394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3394 (by decide) v hb
def cl_3395 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,false),(59,false)]
theorem inp_3395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3395 v hb
def cl_3396 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,false),(59,false)]
theorem inp_3396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3396 (by decide) v hb
def cl_3397 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,false),(59,false)]
theorem inp_3397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3397 (by decide) v hb
def cl_3398 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,false),(59,false)]
theorem inp_3398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3398 (by decide) v hb
def cl_3399 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,false),(59,false)]
theorem inp_3399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3399 (by decide) v hb
def cl_3400 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,false),(55,false),(59,false)]
theorem inp_3400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3400 (by decide) v hb
def cl_3401 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,false),(59,false)]
theorem inp_3401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3401 v hb
def cl_3402 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,false),(59,false)]
theorem inp_3402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3402 (by decide) v hb
def cl_3403 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,false),(59,false)]
theorem inp_3403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3403 v hb
def cl_3404 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,true),(55,false),(59,false)]
theorem inp_3404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3404 (by decide) v hb
def cl_3405 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,false),(59,false)]
theorem inp_3405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3405 (by decide) v hb
def cl_3406 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,true),(55,false),(59,false)]
theorem inp_3406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3406 (by decide) v hb
def cl_3407 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,false),(59,false)]
theorem inp_3407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3407 v hb
def cl_3408 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,true),(55,false),(59,false)]
theorem inp_3408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3408 (by decide) v hb
def cl_3409 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,true),(59,false)]
theorem inp_3409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3409 (by decide) v hb
end Percolation.NReplay
