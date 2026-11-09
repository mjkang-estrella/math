import NInputs177
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11245 : CNF.NClause := [(652,true),(660,true),(663,true),(666,true),(674,false),(679,true)]
theorem inp_11245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 19) (closed_mem 17 19) cl_11245 (by decide) v hb
def cl_11247 : CNF.NClause := [(652,true),(660,true),(663,false),(666,true),(674,true),(679,true)]
theorem inp_11247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 19) (closed_mem 17 19) cl_11247 (by decide) v hb
def cl_11249 : CNF.NClause := [(652,false),(660,true),(663,true),(666,true),(674,true),(679,true)]
theorem inp_11249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 19) (closed_mem 17 19) cl_11249 (by decide) v hb
def cl_11251 : CNF.NClause := [(656,true),(657,true),(658,true),(659,true),(660,false),(681,true)]
theorem inp_11251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 20) (closed_mem 17 20) cl_11251 (by decide) v hb
def cl_11252 : CNF.NClause := [(656,true),(657,true),(658,true),(659,false),(660,true),(681,true)]
theorem inp_11252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 20) (closed_mem 17 20) cl_11252 (by decide) v hb
def cl_11253 : CNF.NClause := [(656,true),(657,true),(658,false),(659,true),(660,true),(681,true)]
theorem inp_11253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 20) (closed_mem 17 20) cl_11253 (by decide) v hb
def cl_11254 : CNF.NClause := [(656,true),(657,false),(658,true),(659,true),(660,true),(681,true)]
theorem inp_11254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 20) (closed_mem 17 20) cl_11254 (by decide) v hb
def cl_11255 : CNF.NClause := [(656,false),(657,true),(658,true),(659,true),(660,true),(681,true)]
theorem inp_11255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 20) (closed_mem 17 20) cl_11255 (by decide) v hb
def cl_11258 : CNF.NClause := [(655,true),(656,true),(662,true),(668,false),(674,true),(677,true)]
theorem inp_11258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 21) (closed_mem 17 21) cl_11258 (by decide) v hb
def cl_11262 : CNF.NClause := [(653,true),(656,true),(664,true),(667,true),(675,true),(679,false)]
theorem inp_11262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 22) (closed_mem 17 22) cl_11262 (by decide) v hb
def cl_11263 : CNF.NClause := [(653,true),(656,true),(664,true),(667,true),(675,false),(679,true)]
theorem inp_11263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 22) (closed_mem 17 22) cl_11263 (by decide) v hb
def cl_11267 : CNF.NClause := [(653,false),(656,true),(664,true),(667,true),(675,true),(679,true)]
theorem inp_11267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 22) (closed_mem 17 22) cl_11267 (by decide) v hb
def cl_11269 : CNF.NClause := [(654,true),(656,true),(663,true),(670,true),(672,false),(678,true)]
theorem inp_11269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 23) (closed_mem 17 23) cl_11269 (by decide) v hb
def cl_11270 : CNF.NClause := [(654,true),(656,true),(663,true),(670,false),(672,true),(678,true)]
theorem inp_11270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 23) (closed_mem 17 23) cl_11270 (by decide) v hb
def cl_11272 : CNF.NClause := [(654,true),(656,false),(663,true),(670,true),(672,true),(678,true)]
theorem inp_11272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 23) (closed_mem 17 23) cl_11272 (by decide) v hb
def cl_11274 : CNF.NClause := [(652,true),(656,true),(665,true),(669,true),(673,true),(680,false)]
theorem inp_11274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 24) (closed_mem 17 24) cl_11274 (by decide) v hb
def cl_11277 : CNF.NClause := [(652,true),(656,true),(665,false),(669,true),(673,true),(680,true)]
theorem inp_11277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 24) (closed_mem 17 24) cl_11277 (by decide) v hb
def cl_11278 : CNF.NClause := [(652,true),(656,false),(665,true),(669,true),(673,true),(680,true)]
theorem inp_11278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 24) (closed_mem 17 24) cl_11278 (by decide) v hb
def cl_11281 : CNF.NClause := [(651,true),(652,true),(653,true),(654,true),(655,false),(681,true)]
theorem inp_11281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 25) (closed_mem 17 25) cl_11281 (by decide) v hb
def cl_11282 : CNF.NClause := [(651,true),(652,true),(653,true),(654,false),(655,true),(681,true)]
theorem inp_11282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 25) (closed_mem 17 25) cl_11282 (by decide) v hb
def cl_11283 : CNF.NClause := [(651,true),(652,true),(653,false),(654,true),(655,true),(681,true)]
theorem inp_11283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 25) (closed_mem 17 25) cl_11283 (by decide) v hb
def cl_11284 : CNF.NClause := [(651,true),(652,false),(653,true),(654,true),(655,true),(681,true)]
theorem inp_11284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 25) (closed_mem 17 25) cl_11284 (by decide) v hb
def cl_11288 : CNF.NClause := [(651,true),(660,true),(664,true),(668,false),(672,true),(680,true)]
theorem inp_11288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 26) (closed_mem 17 26) cl_11288 (by decide) v hb
def cl_11293 : CNF.NClause := [(651,true),(658,true),(665,true),(667,true),(674,false),(678,true)]
theorem inp_11293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 27) (closed_mem 17 27) cl_11293 (by decide) v hb
def cl_11294 : CNF.NClause := [(651,true),(658,true),(665,true),(667,false),(674,true),(678,true)]
theorem inp_11294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 27) (closed_mem 17 27) cl_11294 (by decide) v hb
def cl_11295 : CNF.NClause := [(651,true),(658,true),(665,false),(667,true),(674,true),(678,true)]
theorem inp_11295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 27) (closed_mem 17 27) cl_11295 (by decide) v hb
def cl_11296 : CNF.NClause := [(651,true),(658,false),(665,true),(667,true),(674,true),(678,true)]
theorem inp_11296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 27) (closed_mem 17 27) cl_11296 (by decide) v hb
def cl_11298 : CNF.NClause := [(651,true),(659,true),(662,true),(670,true),(673,true),(679,false)]
theorem inp_11298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 28) (closed_mem 17 28) cl_11298 (by decide) v hb
def cl_11299 : CNF.NClause := [(651,true),(659,true),(662,true),(670,true),(673,false),(679,true)]
theorem inp_11299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 28) (closed_mem 17 28) cl_11299 (by decide) v hb
def cl_11300 : CNF.NClause := [(651,true),(659,true),(662,true),(670,false),(673,true),(679,true)]
theorem inp_11300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 28) (closed_mem 17 28) cl_11300 (by decide) v hb
def cl_11301 : CNF.NClause := [(651,true),(659,true),(662,false),(670,true),(673,true),(679,true)]
theorem inp_11301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 28) (closed_mem 17 28) cl_11301 (by decide) v hb
def cl_11302 : CNF.NClause := [(651,true),(659,false),(662,true),(670,true),(673,true),(679,true)]
theorem inp_11302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 28) (closed_mem 17 28) cl_11302 (by decide) v hb
def cl_11304 : CNF.NClause := [(651,true),(657,true),(663,true),(669,true),(675,true),(677,false)]
theorem inp_11304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 29) (closed_mem 17 29) cl_11304 (by decide) v hb
def cl_11305 : CNF.NClause := [(651,true),(657,true),(663,true),(669,true),(675,false),(677,true)]
theorem inp_11305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 29) (closed_mem 17 29) cl_11305 (by decide) v hb
def cl_11307 : CNF.NClause := [(651,true),(657,true),(663,false),(669,true),(675,true),(677,true)]
theorem inp_11307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 29) (closed_mem 17 29) cl_11307 (by decide) v hb
def cl_11311 : CNF.NClause := [(651,true),(656,true),(661,true),(666,true),(671,false),(676,true)]
theorem inp_11311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 30) (closed_mem 17 30) cl_11311 (by decide) v hb
def cl_11312 : CNF.NClause := [(651,true),(656,true),(661,true),(666,false),(671,true),(676,true)]
theorem inp_11312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 30) (closed_mem 17 30) cl_11312 (by decide) v hb
def cl_11313 : CNF.NClause := [(651,true),(656,true),(661,false),(666,true),(671,true),(676,true)]
theorem inp_11313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 30) (closed_mem 17 30) cl_11313 (by decide) v hb
def cl_11314 : CNF.NClause := [(651,true),(656,false),(661,true),(666,true),(671,true),(676,true)]
theorem inp_11314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 30) (closed_mem 17 30) cl_11314 (by decide) v hb
def cl_11317 : CNF.NClause := [(707,true),(708,true),(709,true),(710,true),(711,false),(712,true)]
theorem inp_11317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 0) (closed_mem 18 0) cl_11317 (by decide) v hb
def cl_11318 : CNF.NClause := [(707,true),(708,true),(709,true),(710,false),(711,true),(712,true)]
theorem inp_11318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11318 v hb
def cl_11319 : CNF.NClause := [(707,true),(708,true),(709,false),(710,true),(711,true),(712,true)]
theorem inp_11319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 0) (closed_mem 18 0) cl_11319 (by decide) v hb
def cl_11320 : CNF.NClause := [(707,true),(708,false),(709,true),(710,true),(711,true),(712,true)]
theorem inp_11320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 0) (closed_mem 18 0) cl_11320 (by decide) v hb
def cl_11323 : CNF.NClause := [(686,true),(691,true),(696,true),(701,true),(706,false),(707,true)]
theorem inp_11323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 1) (closed_mem 18 1) cl_11323 (by decide) v hb
def cl_11324 : CNF.NClause := [(686,true),(691,true),(696,true),(701,false),(706,true),(707,true)]
theorem inp_11324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 1) (closed_mem 18 1) cl_11324 (by decide) v hb
def cl_11325 : CNF.NClause := [(686,true),(691,true),(696,false),(701,true),(706,true),(707,true)]
theorem inp_11325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 1) (closed_mem 18 1) cl_11325 (by decide) v hb
def cl_11326 : CNF.NClause := [(686,true),(691,false),(696,true),(701,true),(706,true),(707,true)]
theorem inp_11326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 1) (closed_mem 18 1) cl_11326 (by decide) v hb
def cl_11327 : CNF.NClause := [(686,false),(691,true),(696,true),(701,true),(706,true),(707,true)]
theorem inp_11327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 1) (closed_mem 18 1) cl_11327 (by decide) v hb
def cl_11329 : CNF.NClause := [(684,true),(689,true),(694,true),(699,true),(704,false),(707,true)]
theorem inp_11329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 2) (closed_mem 18 2) cl_11329 (by decide) v hb
def cl_11330 : CNF.NClause := [(684,true),(689,true),(694,true),(699,false),(704,true),(707,true)]
theorem inp_11330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 2) (closed_mem 18 2) cl_11330 (by decide) v hb
end Percolation.NReplay
