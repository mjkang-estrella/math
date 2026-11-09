import NInputs090
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5302 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5302 v hb
def cl_5303 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5303 (by decide) v hb
def cl_5304 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5304 (by decide) v hb
def cl_5305 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inp_5305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5305 (by decide) v hb
def cl_5306 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inp_5306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5306 (by decide) v hb
def cl_5307 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inp_5307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5307 (by decide) v hb
def cl_5308 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inp_5308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5308 (by decide) v hb
def cl_5309 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,true),(92,false)]
theorem inp_5309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5309 (by decide) v hb
def cl_5310 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,true),(92,false)]
theorem inp_5310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5310 (by decide) v hb
def cl_5312 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,true),(92,false)]
theorem inp_5312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5312 (by decide) v hb
def cl_5313 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5313 (by decide) v hb
def cl_5314 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5314 (by decide) v hb
def cl_5315 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5315 (by decide) v hb
def cl_5316 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5316 (by decide) v hb
def cl_5317 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5317 (by decide) v hb
def cl_5318 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5318 (by decide) v hb
def cl_5319 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5319 (by decide) v hb
def cl_5320 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inp_5320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5320 (by decide) v hb
def cl_5321 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5321 (by decide) v hb
def cl_5322 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5322 (by decide) v hb
def cl_5323 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5323 (by decide) v hb
def cl_5324 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5324 (by decide) v hb
def cl_5325 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5325 (by decide) v hb
def cl_5326 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5326 (by decide) v hb
def cl_5327 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5327 (by decide) v hb
def cl_5328 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inp_5328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5328 (by decide) v hb
def cl_5329 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5329 (by decide) v hb
def cl_5330 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5330 (by decide) v hb
def cl_5331 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5331 (by decide) v hb
def cl_5332 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5332 (by decide) v hb
def cl_5333 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5333 (by decide) v hb
def cl_5334 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5334 (by decide) v hb
def cl_5335 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5335 (by decide) v hb
def cl_5336 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inp_5336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5336 (by decide) v hb
def cl_5337 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5337 (by decide) v hb
def cl_5338 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5338 (by decide) v hb
def cl_5339 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5339 (by decide) v hb
def cl_5340 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5340 (by decide) v hb
def cl_5341 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5341 (by decide) v hb
def cl_5342 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5342 (by decide) v hb
def cl_5343 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5343 (by decide) v hb
def cl_5344 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inp_5344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5344 (by decide) v hb
def cl_5345 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inp_5345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5345 (by decide) v hb
def cl_5346 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inp_5346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5346 (by decide) v hb
def cl_5347 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inp_5347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5347 (by decide) v hb
def cl_5348 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inp_5348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5348 (by decide) v hb
def cl_5350 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,true),(92,true)]
theorem inp_5350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5350 (by decide) v hb
def cl_5351 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,true),(92,true)]
theorem inp_5351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5351 (by decide) v hb
def cl_5352 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,true),(92,true)]
theorem inp_5352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5352 (by decide) v hb
def cl_5353 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5353 (by decide) v hb
end Percolation.NReplay
