import Inputs029
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3271 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,false),(61,false)]
theorem inp_3271 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3271 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3271 (by decide) v h
def cl_3273 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,false),(61,false)]
theorem inp_3273 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3273 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3273 (by decide) v h
def cl_3274 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,false),(61,false)]
theorem inp_3274 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3274 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3274 (by decide) v h
def cl_3275 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,false),(61,false)]
theorem inp_3275 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3275 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3275 (by decide) v h
def cl_3277 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,false),(61,false)]
theorem inp_3277 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3277 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3277 (by decide) v h
def cl_3278 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,true),(40,false),(61,false)]
theorem inp_3278 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3278 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3278 (by decide) v h
def cl_3279 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,true),(40,false),(61,false)]
theorem inp_3279 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3279 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3279 (by decide) v h
def cl_3280 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,true),(40,false),(61,false)]
theorem inp_3280 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3280 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3280 (by decide) v h
def cl_3283 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,true),(61,false)]
theorem inp_3283 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3283 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3283 (by decide) v h
def cl_3285 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3285 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3285 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3285 (by decide) v h
def cl_3286 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3286 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3286 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3286 (by decide) v h
def cl_3287 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3287 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3287 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3287 (by decide) v h
def cl_3288 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,true),(61,false)]
theorem inp_3288 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3288 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3288 (by decide) v h
def cl_3289 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,true),(61,false)]
theorem inp_3289 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3289 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3289 (by decide) v h
def cl_3290 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,true),(61,false)]
theorem inp_3290 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3290 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3290 (by decide) v h
def cl_3293 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,true),(61,false)]
theorem inp_3293 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3293 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3293 (by decide) v h
def cl_3294 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,true),(40,true),(61,false)]
theorem inp_3294 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3294 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3294 (by decide) v h
def cl_3298 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,false),(61,true)]
theorem inp_3298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3298 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3298 (by decide) v h
def cl_3302 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,false),(61,true)]
theorem inp_3302 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3302 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3302 (by decide) v h
def cl_3304 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,false),(61,true)]
theorem inp_3304 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3304 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3304 (by decide) v h
def cl_3307 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,false),(61,true)]
theorem inp_3307 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3307 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3307 (by decide) v h
def cl_3309 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,false),(61,true)]
theorem inp_3309 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3309 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3309 (by decide) v h
def cl_3310 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,true),(40,false),(61,true)]
theorem inp_3310 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3310 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3310 (by decide) v h
def cl_3311 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,true),(40,false),(61,true)]
theorem inp_3311 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3311 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3311 (by decide) v h
def cl_3314 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,true),(61,true)]
theorem inp_3314 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3314 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3314 (by decide) v h
def cl_3317 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,true),(61,true)]
theorem inp_3317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3317 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3317 (by decide) v h
def cl_3318 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,true),(61,true)]
theorem inp_3318 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3318 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3318 (by decide) v h
def cl_3331 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,false),(57,false)]
theorem inp_3331 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3331 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3331 (by decide) v h
def cl_3332 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,false),(57,false)]
theorem inp_3332 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3332 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3332 (by decide) v h
def cl_3335 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,false),(57,false)]
theorem inp_3335 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3335 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3335 (by decide) v h
def cl_3336 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,false),(57,false)]
theorem inp_3336 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3336 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3336 (by decide) v h
def cl_3340 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,false),(57,false)]
theorem inp_3340 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3340 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3340 (by decide) v h
def cl_3344 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,true),(54,false),(57,false)]
theorem inp_3344 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3344 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3344 (by decide) v h
def cl_3348 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,true),(57,false)]
theorem inp_3348 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3348 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3348 (by decide) v h
def cl_3352 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,true),(57,false)]
theorem inp_3352 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3352 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3352 (by decide) v h
def cl_3356 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,true),(57,false)]
theorem inp_3356 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3356 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3356 (by decide) v h
def cl_3364 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,false),(57,true)]
theorem inp_3364 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3364 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3364 (by decide) v h
def cl_3367 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,false),(57,true)]
theorem inp_3367 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3367 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3367 (by decide) v h
def cl_3368 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,false),(57,true)]
theorem inp_3368 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3368 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3368 (by decide) v h
def cl_3371 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,false),(57,true)]
theorem inp_3371 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3371 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3371 (by decide) v h
def cl_3372 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,false),(57,true)]
theorem inp_3372 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3372 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3372 (by decide) v h
def cl_3379 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,true),(57,true)]
theorem inp_3379 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3379 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3379 (by decide) v h
def cl_3380 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,true),(57,true)]
theorem inp_3380 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3380 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3380 (by decide) v h
def cl_3383 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,true),(57,true)]
theorem inp_3383 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3383 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3383 (by decide) v h
def cl_3387 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,true),(57,true)]
theorem inp_3387 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3387 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3387 (by decide) v h
def cl_3391 : CNF.NClause := [(114,false),(35,false),(36,true),(42,true),(48,true),(54,true),(57,true)]
theorem inp_3391 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3391 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3391 (by decide) v h
def cl_3392 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,true),(57,true)]
theorem inp_3392 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3392 := by
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) cl_3392 (by decide) v h
def cl_3395 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,false),(59,false)]
theorem inp_3395 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3395 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3395 (by decide) v h
def cl_3401 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,false),(59,false)]
theorem inp_3401 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3401 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3401 (by decide) v h
def cl_3403 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,false),(59,false)]
theorem inp_3403 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3403 := by
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3403 (by decide) v h
end Percolation.Replay
