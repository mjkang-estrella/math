import NInputs001
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_246 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,true),(25,true)]
theorem inp_246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_246 (by decide) v hb
def cl_247 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,true),(25,true)]
theorem inp_247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_247 v hb
def cl_248 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,false),(23,true),(25,true)]
theorem inp_248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_248 v hb
def cl_249 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,true),(23,true),(25,true)]
theorem inp_249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_249 (by decide) v hb
def cl_250 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,true),(23,true),(25,true)]
theorem inp_250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_250 (by decide) v hb
def cl_251 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,true),(25,true)]
theorem inp_251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_251 v hb
def cl_252 : CNF.NClause := [(65,false),(3,true),(8,true),(13,false),(18,true),(23,true),(25,true)]
theorem inp_252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_252 v hb
def cl_253 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,true),(25,true)]
theorem inp_253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_253 v hb
def cl_254 : CNF.NClause := [(65,false),(3,true),(8,false),(13,true),(18,true),(23,true),(25,true)]
theorem inp_254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_254 (by decide) v hb
def cl_255 : CNF.NClause := [(65,false),(3,false),(8,true),(13,true),(18,true),(23,true),(25,true)]
theorem inp_255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_255 v hb
def cl_256 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,true),(23,true),(25,true)]
theorem inp_256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_256 v hb
def cl_289 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,false),(21,false),(25,true)]
theorem inp_289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_289 v hb
def cl_290 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,false),(25,true)]
theorem inp_290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_290 (by decide) v hb
def cl_291 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,false),(25,true)]
theorem inp_291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_291 v hb
def cl_292 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,false),(21,false),(25,true)]
theorem inp_292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_292 (by decide) v hb
def cl_293 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,false),(25,true)]
theorem inp_293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_293 v hb
def cl_294 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,false),(21,false),(25,true)]
theorem inp_294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_294 (by decide) v hb
def cl_295 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,false),(21,false),(25,true)]
theorem inp_295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_295 (by decide) v hb
def cl_296 : CNF.NClause := [(66,true),(1,true),(6,true),(11,true),(16,false),(21,false),(25,true)]
theorem inp_296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_296 (by decide) v hb
def cl_297 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,true),(21,false),(25,true)]
theorem inp_297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_297 (by decide) v hb
def cl_298 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,false),(25,true)]
theorem inp_298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_298 (by decide) v hb
def cl_299 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,false),(25,true)]
theorem inp_299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_299 v hb
def cl_300 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,true),(21,false),(25,true)]
theorem inp_300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_300 (by decide) v hb
def cl_301 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,false),(25,true)]
theorem inp_301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_301 v hb
def cl_302 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,true),(21,false),(25,true)]
theorem inp_302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_302 (by decide) v hb
def cl_303 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,true),(21,false),(25,true)]
theorem inp_303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_303 (by decide) v hb
def cl_304 : CNF.NClause := [(66,false),(1,true),(6,true),(11,true),(16,true),(21,false),(25,true)]
theorem inp_304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_304 (by decide) v hb
def cl_305 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,false),(21,true),(25,true)]
theorem inp_305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_305 (by decide) v hb
def cl_306 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,true),(25,true)]
theorem inp_306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_306 v hb
def cl_307 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,true),(25,true)]
theorem inp_307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_307 v hb
def cl_308 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,false),(21,true),(25,true)]
theorem inp_308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_308 (by decide) v hb
def cl_309 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,true),(25,true)]
theorem inp_309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_309 v hb
def cl_310 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,false),(21,true),(25,true)]
theorem inp_310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_310 (by decide) v hb
def cl_311 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,false),(21,true),(25,true)]
theorem inp_311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_311 (by decide) v hb
def cl_312 : CNF.NClause := [(66,false),(1,true),(6,true),(11,true),(16,false),(21,true),(25,true)]
theorem inp_312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_312 (by decide) v hb
def cl_313 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,true),(21,true),(25,true)]
theorem inp_313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_313 v hb
def cl_314 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,true),(25,true)]
theorem inp_314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_314 v hb
def cl_315 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,true),(25,true)]
theorem inp_315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_315 v hb
def cl_316 : CNF.NClause := [(66,false),(1,true),(6,true),(11,false),(16,true),(21,true),(25,true)]
theorem inp_316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_316 (by decide) v hb
def cl_317 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,true),(25,true)]
theorem inp_317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_317 v hb
def cl_318 : CNF.NClause := [(66,false),(1,true),(6,false),(11,true),(16,true),(21,true),(25,true)]
theorem inp_318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_318 (by decide) v hb
def cl_319 : CNF.NClause := [(66,false),(1,false),(6,true),(11,true),(16,true),(21,true),(25,true)]
theorem inp_319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_319 (by decide) v hb
def cl_320 : CNF.NClause := [(66,false),(1,true),(6,true),(11,true),(16,true),(21,true),(25,true)]
theorem inp_320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_320 (by decide) v hb
def cl_353 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,false),(24,false),(30,true)]
theorem inp_353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_353 v hb
def cl_354 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,false),(24,false),(30,true)]
theorem inp_354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_354 v hb
def cl_355 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,false),(24,false),(30,true)]
theorem inp_355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_355 v hb
def cl_356 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,false),(30,true)]
theorem inp_356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_356 v hb
def cl_357 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,false),(24,false),(30,true)]
theorem inp_357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_357 (by decide) v hb
def cl_358 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,false),(24,false),(30,true)]
theorem inp_358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_358 v hb
def cl_359 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,false),(24,false),(30,true)]
theorem inp_359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_359 v hb
end Percolation.NReplay
