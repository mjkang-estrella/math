import NInputs109
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6283 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6283 v hb
def cl_6284 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6284 (by decide) v hb
def cl_6285 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6285 v hb
def cl_6286 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6286 (by decide) v hb
def cl_6287 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6287 (by decide) v hb
def cl_6288 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6288 (by decide) v hb
def cl_6289 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6289 v hb
def cl_6290 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6290 v hb
def cl_6291 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6291 v hb
def cl_6292 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6292 (by decide) v hb
def cl_6293 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6293 v hb
def cl_6294 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6294 v hb
def cl_6295 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6295 v hb
def cl_6296 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6296 (by decide) v hb
def cl_6297 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6297 (by decide) v hb
def cl_6298 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6298 v hb
def cl_6299 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6299 (by decide) v hb
def cl_6300 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6300 (by decide) v hb
def cl_6301 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6301 (by decide) v hb
def cl_6302 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6302 v hb
def cl_6303 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6303 (by decide) v hb
def cl_6304 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6304 (by decide) v hb
def cl_6305 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6305 (by decide) v hb
def cl_6306 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6306 v hb
def cl_6307 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6307 (by decide) v hb
def cl_6308 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6308 (by decide) v hb
def cl_6309 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6309 (by decide) v hb
def cl_6310 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6310 v hb
def cl_6311 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6311 (by decide) v hb
def cl_6312 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6312 (by decide) v hb
def cl_6313 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6313 (by decide) v hb
def cl_6314 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6314 (by decide) v hb
def cl_6315 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6315 (by decide) v hb
def cl_6316 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6316 (by decide) v hb
def cl_6317 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6317 (by decide) v hb
def cl_6318 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6318 (by decide) v hb
def cl_6319 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6319 (by decide) v hb
def cl_6320 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inp_6320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6320 (by decide) v hb
def cl_6321 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inp_6321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6321 (by decide) v hb
def cl_6322 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inp_6322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6322 (by decide) v hb
def cl_6323 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inp_6323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6323 (by decide) v hb
def cl_6324 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inp_6324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6324 (by decide) v hb
def cl_6326 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,true),(91,false)]
theorem inp_6326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6326 (by decide) v hb
def cl_6327 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,true),(91,false)]
theorem inp_6327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6327 (by decide) v hb
def cl_6328 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,true),(91,false)]
theorem inp_6328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6328 (by decide) v hb
def cl_6329 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6329 (by decide) v hb
def cl_6330 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6330 (by decide) v hb
def cl_6331 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6331 (by decide) v hb
def cl_6332 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6332 (by decide) v hb
def cl_6333 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6333 (by decide) v hb
end Percolation.NReplay
