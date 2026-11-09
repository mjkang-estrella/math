import NInputs089
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5252 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5252 (by decide) v hb
def cl_5253 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5253 (by decide) v hb
def cl_5254 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5254 (by decide) v hb
def cl_5255 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5255 (by decide) v hb
def cl_5256 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5256 (by decide) v hb
def cl_5257 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5257 (by decide) v hb
def cl_5258 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5258 (by decide) v hb
def cl_5259 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5259 (by decide) v hb
def cl_5260 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5260 (by decide) v hb
def cl_5261 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5261 (by decide) v hb
def cl_5262 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5262 (by decide) v hb
def cl_5263 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5263 (by decide) v hb
def cl_5264 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inp_5264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5264 (by decide) v hb
def cl_5265 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5265 (by decide) v hb
def cl_5266 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5266 v hb
def cl_5267 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5267 (by decide) v hb
def cl_5268 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5268 v hb
def cl_5269 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5269 (by decide) v hb
def cl_5270 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5270 v hb
def cl_5271 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5271 (by decide) v hb
def cl_5272 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5272 v hb
def cl_5273 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5273 (by decide) v hb
def cl_5274 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5274 (by decide) v hb
def cl_5275 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5275 (by decide) v hb
def cl_5276 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5276 (by decide) v hb
def cl_5277 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5277 (by decide) v hb
def cl_5278 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5278 (by decide) v hb
def cl_5279 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5279 (by decide) v hb
def cl_5280 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inp_5280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5280 (by decide) v hb
def cl_5281 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5281 (by decide) v hb
def cl_5282 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5282 (by decide) v hb
def cl_5283 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5283 (by decide) v hb
def cl_5284 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5284 (by decide) v hb
def cl_5285 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5285 (by decide) v hb
def cl_5286 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5286 (by decide) v hb
def cl_5287 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5287 (by decide) v hb
def cl_5288 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inp_5288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5288 (by decide) v hb
def cl_5289 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5289 (by decide) v hb
def cl_5290 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5290 (by decide) v hb
def cl_5291 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5291 (by decide) v hb
def cl_5292 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5292 (by decide) v hb
def cl_5293 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5293 (by decide) v hb
def cl_5294 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5294 (by decide) v hb
def cl_5295 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5295 (by decide) v hb
def cl_5296 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inp_5296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5296 (by decide) v hb
def cl_5297 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5297 (by decide) v hb
def cl_5298 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5298 v hb
def cl_5299 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5299 (by decide) v hb
def cl_5300 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5300 (by decide) v hb
def cl_5301 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5301 (by decide) v hb
end Percolation.NReplay
