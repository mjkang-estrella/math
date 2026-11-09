import NInputs072
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4383 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4383 (by decide) v hb
def cl_4384 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4384 (by decide) v hb
def cl_4385 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4385 (by decide) v hb
def cl_4386 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4386 (by decide) v hb
def cl_4387 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4387 (by decide) v hb
def cl_4388 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4388 (by decide) v hb
def cl_4389 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4389 (by decide) v hb
def cl_4390 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4390 (by decide) v hb
def cl_4391 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4391 (by decide) v hb
def cl_4392 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inp_4392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4392 (by decide) v hb
def cl_4393 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4393 (by decide) v hb
def cl_4394 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4394 v hb
def cl_4395 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4395 (by decide) v hb
def cl_4396 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4396 v hb
def cl_4397 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4397 (by decide) v hb
def cl_4398 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4398 v hb
def cl_4399 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4399 (by decide) v hb
def cl_4400 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4400 (by decide) v hb
def cl_4401 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4401 (by decide) v hb
def cl_4402 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4402 (by decide) v hb
def cl_4403 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4403 (by decide) v hb
def cl_4404 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4404 (by decide) v hb
def cl_4405 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4405 (by decide) v hb
def cl_4406 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4406 (by decide) v hb
def cl_4407 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4407 (by decide) v hb
def cl_4408 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inp_4408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4408 (by decide) v hb
def cl_4409 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4409 (by decide) v hb
def cl_4410 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4410 v hb
def cl_4411 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4411 (by decide) v hb
def cl_4412 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4412 (by decide) v hb
def cl_4413 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4413 (by decide) v hb
def cl_4414 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4414 (by decide) v hb
def cl_4415 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4415 (by decide) v hb
def cl_4416 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4416 (by decide) v hb
def cl_4417 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4417 v hb
def cl_4418 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4418 v hb
def cl_4419 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4419 (by decide) v hb
def cl_4420 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4420 (by decide) v hb
def cl_4421 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4421 (by decide) v hb
def cl_4422 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4422 (by decide) v hb
def cl_4424 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4424 (by decide) v hb
def cl_4425 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4425 (by decide) v hb
def cl_4426 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4426 (by decide) v hb
def cl_4427 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4427 (by decide) v hb
def cl_4428 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4428 (by decide) v hb
def cl_4429 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4429 (by decide) v hb
def cl_4430 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4430 (by decide) v hb
def cl_4431 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4431 (by decide) v hb
def cl_4432 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inp_4432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4432 (by decide) v hb
def cl_4433 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4433 (by decide) v hb
end Percolation.NReplay
