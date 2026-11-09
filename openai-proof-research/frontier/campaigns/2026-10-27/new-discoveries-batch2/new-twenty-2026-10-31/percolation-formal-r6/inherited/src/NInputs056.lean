import NInputs055
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3410 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,true),(59,false)]
theorem inp_3410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3410 (by decide) v hb
def cl_3411 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,true),(59,false)]
theorem inp_3411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3411 (by decide) v hb
def cl_3412 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,true),(59,false)]
theorem inp_3412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3412 (by decide) v hb
def cl_3413 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,true),(59,false)]
theorem inp_3413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3413 (by decide) v hb
def cl_3414 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,true),(59,false)]
theorem inp_3414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3414 (by decide) v hb
def cl_3415 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,true),(59,false)]
theorem inp_3415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3415 (by decide) v hb
def cl_3416 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,false),(55,true),(59,false)]
theorem inp_3416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3416 (by decide) v hb
def cl_3417 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,true),(59,false)]
theorem inp_3417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3417 v hb
def cl_3418 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,true),(59,false)]
theorem inp_3418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3418 (by decide) v hb
def cl_3419 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,true),(59,false)]
theorem inp_3419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3419 v hb
def cl_3420 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,true),(55,true),(59,false)]
theorem inp_3420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3420 (by decide) v hb
def cl_3421 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,true),(59,false)]
theorem inp_3421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3421 (by decide) v hb
def cl_3422 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,true),(55,true),(59,false)]
theorem inp_3422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3422 (by decide) v hb
def cl_3423 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,true),(59,false)]
theorem inp_3423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3423 v hb
def cl_3424 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,true),(59,false)]
theorem inp_3424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3424 v hb
def cl_3425 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,false),(59,true)]
theorem inp_3425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3425 (by decide) v hb
def cl_3426 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,false),(59,true)]
theorem inp_3426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3426 (by decide) v hb
def cl_3427 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,false),(59,true)]
theorem inp_3427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3427 (by decide) v hb
def cl_3428 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,false),(59,true)]
theorem inp_3428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3428 (by decide) v hb
def cl_3429 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,false),(59,true)]
theorem inp_3429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3429 (by decide) v hb
def cl_3430 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,false),(59,true)]
theorem inp_3430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3430 (by decide) v hb
def cl_3431 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,false),(59,true)]
theorem inp_3431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3431 (by decide) v hb
def cl_3432 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,false),(55,false),(59,true)]
theorem inp_3432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3432 (by decide) v hb
def cl_3433 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,false),(59,true)]
theorem inp_3433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3433 (by decide) v hb
def cl_3434 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,false),(59,true)]
theorem inp_3434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3434 (by decide) v hb
def cl_3435 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,false),(59,true)]
theorem inp_3435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3435 v hb
def cl_3436 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,true),(55,false),(59,true)]
theorem inp_3436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3436 v hb
def cl_3437 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,false),(59,true)]
theorem inp_3437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3437 (by decide) v hb
def cl_3438 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,true),(55,false),(59,true)]
theorem inp_3438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3438 (by decide) v hb
def cl_3439 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,false),(59,true)]
theorem inp_3439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3439 (by decide) v hb
def cl_3440 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,false),(59,true)]
theorem inp_3440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3440 (by decide) v hb
def cl_3441 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,true),(59,true)]
theorem inp_3441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3441 (by decide) v hb
def cl_3442 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,true),(59,true)]
theorem inp_3442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3442 (by decide) v hb
def cl_3443 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,true),(59,true)]
theorem inp_3443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3443 (by decide) v hb
def cl_3444 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,true),(59,true)]
theorem inp_3444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3444 (by decide) v hb
def cl_3445 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,true),(59,true)]
theorem inp_3445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3445 (by decide) v hb
def cl_3446 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,true),(59,true)]
theorem inp_3446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3446 (by decide) v hb
def cl_3447 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,true),(59,true)]
theorem inp_3447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3447 (by decide) v hb
def cl_3448 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,false),(55,true),(59,true)]
theorem inp_3448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3448 (by decide) v hb
def cl_3449 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,true),(59,true)]
theorem inp_3449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3449 (by decide) v hb
def cl_3450 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,true),(59,true)]
theorem inp_3450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3450 (by decide) v hb
def cl_3451 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,true),(59,true)]
theorem inp_3451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3451 (by decide) v hb
def cl_3452 : CNF.NClause := [(115,false),(33,true),(36,true),(44,false),(47,true),(55,true),(59,true)]
theorem inp_3452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3452 (by decide) v hb
def cl_3453 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,true),(59,true)]
theorem inp_3453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3453 (by decide) v hb
def cl_3454 : CNF.NClause := [(115,false),(33,true),(36,false),(44,true),(47,true),(55,true),(59,true)]
theorem inp_3454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3454 (by decide) v hb
def cl_3455 : CNF.NClause := [(115,false),(33,false),(36,true),(44,true),(47,true),(55,true),(59,true)]
theorem inp_3455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) cl_3455 (by decide) v hb
def cl_3456 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,true),(59,true)]
theorem inp_3456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3456 v hb
def cl_3457 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3457 v hb
def cl_3458 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3458 v hb
def cl_3459 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,false),(58,false)]
theorem inp_3459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3459 v hb
end Percolation.NReplay
