import NInputs071
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4330 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4330 (by decide) v hb
def cl_4331 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4331 (by decide) v hb
def cl_4332 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4332 (by decide) v hb
def cl_4333 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4333 (by decide) v hb
def cl_4334 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4334 (by decide) v hb
def cl_4335 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4335 (by decide) v hb
def cl_4336 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4336 (by decide) v hb
def cl_4337 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4337 (by decide) v hb
def cl_4338 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4338 (by decide) v hb
def cl_4339 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4339 (by decide) v hb
def cl_4340 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4340 (by decide) v hb
def cl_4341 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4341 (by decide) v hb
def cl_4342 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4342 (by decide) v hb
def cl_4343 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4343 (by decide) v hb
def cl_4344 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inp_4344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4344 (by decide) v hb
def cl_4346 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,true),(87,true)]
theorem inp_4346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4346 (by decide) v hb
def cl_4348 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,true),(87,true)]
theorem inp_4348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4348 (by decide) v hb
def cl_4350 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,true),(87,true)]
theorem inp_4350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4350 (by decide) v hb
def cl_4351 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,true),(84,true),(87,true)]
theorem inp_4351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4351 (by decide) v hb
def cl_4352 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,true),(87,true)]
theorem inp_4352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4352 (by decide) v hb
def cl_4353 : CNF.NClause := [(34,true),(3,false),(65,false),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4353 (by decide) v hb
def cl_4354 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4354 v hb
def cl_4355 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4355 (by decide) v hb
def cl_4356 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4356 (by decide) v hb
def cl_4357 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4357 (by decide) v hb
def cl_4358 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4358 (by decide) v hb
def cl_4359 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4359 (by decide) v hb
def cl_4360 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4360 (by decide) v hb
def cl_4361 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4361 (by decide) v hb
def cl_4362 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4362 v hb
def cl_4363 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4363 (by decide) v hb
def cl_4364 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4364 v hb
def cl_4365 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4365 (by decide) v hb
def cl_4366 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4366 (by decide) v hb
def cl_4367 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4367 (by decide) v hb
def cl_4368 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4368 (by decide) v hb
def cl_4369 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4369 (by decide) v hb
def cl_4370 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4370 (by decide) v hb
def cl_4371 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4371 (by decide) v hb
def cl_4372 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4372 (by decide) v hb
def cl_4373 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4373 (by decide) v hb
def cl_4374 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4374 (by decide) v hb
def cl_4375 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4375 (by decide) v hb
def cl_4376 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inp_4376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4376 (by decide) v hb
def cl_4377 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4377 (by decide) v hb
def cl_4378 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4378 v hb
def cl_4379 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4379 (by decide) v hb
def cl_4380 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4380 v hb
def cl_4381 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4381 (by decide) v hb
def cl_4382 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4382 (by decide) v hb
end Percolation.NReplay
