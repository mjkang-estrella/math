import NInputs070
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4277 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4277 (by decide) v hb
def cl_4278 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4278 (by decide) v hb
def cl_4279 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4279 (by decide) v hb
def cl_4280 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4280 (by decide) v hb
def cl_4281 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4281 (by decide) v hb
def cl_4282 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4282 (by decide) v hb
def cl_4283 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4283 (by decide) v hb
def cl_4284 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4284 (by decide) v hb
def cl_4285 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4285 (by decide) v hb
def cl_4286 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4286 (by decide) v hb
def cl_4287 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4287 (by decide) v hb
def cl_4288 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inp_4288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4288 (by decide) v hb
def cl_4289 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4289 (by decide) v hb
def cl_4290 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4290 (by decide) v hb
def cl_4291 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4291 (by decide) v hb
def cl_4292 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4292 (by decide) v hb
def cl_4293 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4293 (by decide) v hb
def cl_4294 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4294 (by decide) v hb
def cl_4295 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4295 (by decide) v hb
def cl_4296 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inp_4296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4296 (by decide) v hb
def cl_4297 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inp_4297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4297 (by decide) v hb
def cl_4298 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inp_4298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4298 (by decide) v hb
def cl_4299 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inp_4299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4299 (by decide) v hb
def cl_4300 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inp_4300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4300 (by decide) v hb
def cl_4301 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,false),(87,true)]
theorem inp_4301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4301 (by decide) v hb
def cl_4302 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,false),(87,true)]
theorem inp_4302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4302 (by decide) v hb
def cl_4304 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,false),(87,true)]
theorem inp_4304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4304 (by decide) v hb
def cl_4305 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4305 (by decide) v hb
def cl_4306 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4306 (by decide) v hb
def cl_4307 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4307 (by decide) v hb
def cl_4308 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4308 (by decide) v hb
def cl_4309 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4309 (by decide) v hb
def cl_4310 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4310 (by decide) v hb
def cl_4311 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4311 (by decide) v hb
def cl_4312 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inp_4312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4312 (by decide) v hb
def cl_4313 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inp_4313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4313 (by decide) v hb
def cl_4314 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inp_4314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4314 (by decide) v hb
def cl_4315 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inp_4315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4315 (by decide) v hb
def cl_4316 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inp_4316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4316 (by decide) v hb
def cl_4318 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,false),(87,true)]
theorem inp_4318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4318 (by decide) v hb
def cl_4320 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,false),(87,true)]
theorem inp_4320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4320 (by decide) v hb
def cl_4321 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4321 (by decide) v hb
def cl_4322 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4322 (by decide) v hb
def cl_4323 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4323 (by decide) v hb
def cl_4324 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4324 (by decide) v hb
def cl_4325 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4325 (by decide) v hb
def cl_4326 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4326 (by decide) v hb
def cl_4327 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4327 (by decide) v hb
def cl_4328 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inp_4328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4328 (by decide) v hb
def cl_4329 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inp_4329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4329 (by decide) v hb
end Percolation.NReplay
