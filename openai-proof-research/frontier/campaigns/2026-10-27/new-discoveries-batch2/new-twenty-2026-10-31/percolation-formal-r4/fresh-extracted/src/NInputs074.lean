import NInputs073
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4434 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4434 (by decide) v hb
def cl_4435 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4435 (by decide) v hb
def cl_4436 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4436 (by decide) v hb
def cl_4437 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4437 (by decide) v hb
def cl_4438 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4438 (by decide) v hb
def cl_4439 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4439 (by decide) v hb
def cl_4440 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inp_4440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4440 (by decide) v hb
def cl_4441 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4441 (by decide) v hb
def cl_4442 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4442 (by decide) v hb
def cl_4443 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4443 (by decide) v hb
def cl_4444 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4444 (by decide) v hb
def cl_4445 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4445 (by decide) v hb
def cl_4446 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4446 (by decide) v hb
def cl_4447 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4447 (by decide) v hb
def cl_4448 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inp_4448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4448 (by decide) v hb
def cl_4449 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4449 (by decide) v hb
def cl_4450 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4450 (by decide) v hb
def cl_4451 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4451 (by decide) v hb
def cl_4452 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4452 (by decide) v hb
def cl_4453 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4453 (by decide) v hb
def cl_4454 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4454 (by decide) v hb
def cl_4455 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4455 (by decide) v hb
def cl_4456 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inp_4456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4456 (by decide) v hb
def cl_4457 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4457 (by decide) v hb
def cl_4458 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4458 v hb
def cl_4459 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4459 (by decide) v hb
def cl_4460 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4460 (by decide) v hb
def cl_4461 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4461 (by decide) v hb
def cl_4462 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4462 (by decide) v hb
def cl_4463 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4463 (by decide) v hb
def cl_4464 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4464 (by decide) v hb
def cl_4465 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4465 (by decide) v hb
def cl_4466 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4466 (by decide) v hb
def cl_4467 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4467 (by decide) v hb
def cl_4468 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4468 (by decide) v hb
def cl_4469 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4469 (by decide) v hb
def cl_4470 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4470 (by decide) v hb
def cl_4471 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4471 (by decide) v hb
def cl_4472 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inp_4472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4472 (by decide) v hb
def cl_4473 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4473 (by decide) v hb
def cl_4474 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4474 v hb
def cl_4475 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4475 (by decide) v hb
def cl_4476 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4476 (by decide) v hb
def cl_4477 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4477 (by decide) v hb
def cl_4478 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4478 (by decide) v hb
def cl_4479 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4479 (by decide) v hb
def cl_4480 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4480 (by decide) v hb
def cl_4481 : CNF.NClause := [(35,true),(4,false),(63,false),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4481 v hb
def cl_4482 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4482 (by decide) v hb
def cl_4483 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4483 v hb
end Percolation.NReplay
