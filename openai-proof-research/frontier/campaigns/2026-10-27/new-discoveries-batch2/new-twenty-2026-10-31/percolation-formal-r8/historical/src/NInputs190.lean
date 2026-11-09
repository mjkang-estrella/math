import NInputs189
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12291 : CNF.NClause := [(839,true),(846,true),(848,false),(855,true),(857,true),(864,true)]
theorem inp_12291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 7) (closed_mem 23 7) cl_12291 (by decide) v hb
def cl_12292 : CNF.NClause := [(839,true),(846,false),(848,true),(855,true),(857,true),(864,true)]
theorem inp_12292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 7) (closed_mem 23 7) cl_12292 (by decide) v hb
def cl_12293 : CNF.NClause := [(839,false),(846,true),(848,true),(855,true),(857,true),(864,true)]
theorem inp_12293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 7) (closed_mem 23 7) cl_12293 (by decide) v hb
def cl_12294 : CNF.NClause := [(840,true),(843,true),(851,true),(854,true),(857,true),(865,false)]
theorem inp_12294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 8) (closed_mem 23 8) cl_12294 (by decide) v hb
def cl_12295 : CNF.NClause := [(840,true),(843,true),(851,true),(854,true),(857,false),(865,true)]
theorem inp_12295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 8) (closed_mem 23 8) cl_12295 (by decide) v hb
def cl_12297 : CNF.NClause := [(840,true),(843,true),(851,false),(854,true),(857,true),(865,true)]
theorem inp_12297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 8) (closed_mem 23 8) cl_12297 (by decide) v hb
def cl_12299 : CNF.NClause := [(840,false),(843,true),(851,true),(854,true),(857,true),(865,true)]
theorem inp_12299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 8) (closed_mem 23 8) cl_12299 (by decide) v hb
def cl_12302 : CNF.NClause := [(838,true),(844,true),(850,true),(856,false),(857,true),(863,true)]
theorem inp_12302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 9) (closed_mem 23 9) cl_12302 (by decide) v hb
def cl_12305 : CNF.NClause := [(838,false),(844,true),(850,true),(856,true),(857,true),(863,true)]
theorem inp_12305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 9) (closed_mem 23 9) cl_12305 (by decide) v hb
def cl_12307 : CNF.NClause := [(847,true),(848,true),(849,true),(850,true),(851,false),(867,true)]
theorem inp_12307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 10) (closed_mem 23 10) cl_12307 (by decide) v hb
def cl_12308 : CNF.NClause := [(847,true),(848,true),(849,true),(850,false),(851,true),(867,true)]
theorem inp_12308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 10) (closed_mem 23 10) cl_12308 (by decide) v hb
def cl_12310 : CNF.NClause := [(847,true),(848,false),(849,true),(850,true),(851,true),(867,true)]
theorem inp_12310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 10) (closed_mem 23 10) cl_12310 (by decide) v hb
def cl_12313 : CNF.NClause := [(841,true),(844,true),(847,true),(855,true),(858,false),(865,true)]
theorem inp_12313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 11) (closed_mem 23 11) cl_12313 (by decide) v hb
def cl_12315 : CNF.NClause := [(841,true),(844,true),(847,false),(855,true),(858,true),(865,true)]
theorem inp_12315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 11) (closed_mem 23 11) cl_12315 (by decide) v hb
def cl_12319 : CNF.NClause := [(839,true),(843,true),(847,true),(856,true),(860,false),(866,true)]
theorem inp_12319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 12) (closed_mem 23 12) cl_12319 (by decide) v hb
def cl_12327 : CNF.NClause := [(840,true),(846,true),(847,false),(853,true),(859,true),(863,true)]
theorem inp_12327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 13) (closed_mem 23 13) cl_12327 (by decide) v hb
def cl_12330 : CNF.NClause := [(838,true),(845,true),(847,true),(854,true),(861,true),(864,false)]
theorem inp_12330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 14) (closed_mem 23 14) cl_12330 (by decide) v hb
def cl_12334 : CNF.NClause := [(838,true),(845,false),(847,true),(854,true),(861,true),(864,true)]
theorem inp_12334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 14) (closed_mem 23 14) cl_12334 (by decide) v hb
def cl_12337 : CNF.NClause := [(852,true),(853,true),(854,true),(855,true),(856,false),(867,true)]
theorem inp_12337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 15) (closed_mem 23 15) cl_12337 (by decide) v hb
def cl_12340 : CNF.NClause := [(852,true),(853,false),(854,true),(855,true),(856,true),(867,true)]
theorem inp_12340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 15) (closed_mem 23 15) cl_12340 (by decide) v hb
def cl_12341 : CNF.NClause := [(852,false),(853,true),(854,true),(855,true),(856,true),(867,true)]
theorem inp_12341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 15) (closed_mem 23 15) cl_12341 (by decide) v hb
def cl_12342 : CNF.NClause := [(841,true),(843,true),(850,true),(852,true),(859,true),(864,false)]
theorem inp_12342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 16) (closed_mem 23 16) cl_12342 (by decide) v hb
def cl_12345 : CNF.NClause := [(841,true),(843,true),(850,false),(852,true),(859,true),(864,true)]
theorem inp_12345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 16) (closed_mem 23 16) cl_12345 (by decide) v hb
def cl_12347 : CNF.NClause := [(841,false),(843,true),(850,true),(852,true),(859,true),(864,true)]
theorem inp_12347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 16) (closed_mem 23 16) cl_12347 (by decide) v hb
def cl_12349 : CNF.NClause := [(839,true),(845,true),(851,true),(852,true),(858,false),(863,true)]
theorem inp_12349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 17) (closed_mem 23 17) cl_12349 (by decide) v hb
def cl_12351 : CNF.NClause := [(839,true),(845,true),(851,false),(852,true),(858,true),(863,true)]
theorem inp_12351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 17) (closed_mem 23 17) cl_12351 (by decide) v hb
def cl_12352 : CNF.NClause := [(839,true),(845,false),(851,true),(852,true),(858,true),(863,true)]
theorem inp_12352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 17) (closed_mem 23 17) cl_12352 (by decide) v hb
def cl_12353 : CNF.NClause := [(839,false),(845,true),(851,true),(852,true),(858,true),(863,true)]
theorem inp_12353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 17) (closed_mem 23 17) cl_12353 (by decide) v hb
def cl_12357 : CNF.NClause := [(840,true),(844,true),(848,false),(852,true),(861,true),(866,true)]
theorem inp_12357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 18) (closed_mem 23 18) cl_12357 (by decide) v hb
def cl_12358 : CNF.NClause := [(840,true),(844,false),(848,true),(852,true),(861,true),(866,true)]
theorem inp_12358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 18) (closed_mem 23 18) cl_12358 (by decide) v hb
def cl_12361 : CNF.NClause := [(838,true),(846,true),(849,true),(852,true),(860,false),(865,true)]
theorem inp_12361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 19) (closed_mem 23 19) cl_12361 (by decide) v hb
def cl_12368 : CNF.NClause := [(842,true),(843,true),(844,true),(845,false),(846,true),(867,true)]
theorem inp_12368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 20) (closed_mem 23 20) cl_12368 (by decide) v hb
def cl_12369 : CNF.NClause := [(842,true),(843,true),(844,false),(845,true),(846,true),(867,true)]
theorem inp_12369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 20) (closed_mem 23 20) cl_12369 (by decide) v hb
def cl_12373 : CNF.NClause := [(841,true),(842,true),(848,true),(854,true),(860,false),(863,true)]
theorem inp_12373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 21) (closed_mem 23 21) cl_12373 (by decide) v hb
def cl_12382 : CNF.NClause := [(839,true),(842,false),(850,true),(853,true),(861,true),(865,true)]
theorem inp_12382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 22) (closed_mem 23 22) cl_12382 (by decide) v hb
def cl_12385 : CNF.NClause := [(840,true),(842,true),(849,true),(856,true),(858,false),(864,true)]
theorem inp_12385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 23) (closed_mem 23 23) cl_12385 (by decide) v hb
def cl_12388 : CNF.NClause := [(840,true),(842,false),(849,true),(856,true),(858,true),(864,true)]
theorem inp_12388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 23) (closed_mem 23 23) cl_12388 (by decide) v hb
def cl_12390 : CNF.NClause := [(838,true),(842,true),(851,true),(855,true),(859,true),(866,false)]
theorem inp_12390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 24) (closed_mem 23 24) cl_12390 (by decide) v hb
def cl_12394 : CNF.NClause := [(838,true),(842,false),(851,true),(855,true),(859,true),(866,true)]
theorem inp_12394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 24) (closed_mem 23 24) cl_12394 (by decide) v hb
def cl_12398 : CNF.NClause := [(837,true),(838,true),(839,true),(840,false),(841,true),(867,true)]
theorem inp_12398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 25) (closed_mem 23 25) cl_12398 (by decide) v hb
def cl_12399 : CNF.NClause := [(837,true),(838,true),(839,false),(840,true),(841,true),(867,true)]
theorem inp_12399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 25) (closed_mem 23 25) cl_12399 (by decide) v hb
def cl_12400 : CNF.NClause := [(837,true),(838,false),(839,true),(840,true),(841,true),(867,true)]
theorem inp_12400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 25) (closed_mem 23 25) cl_12400 (by decide) v hb
def cl_12404 : CNF.NClause := [(837,true),(846,true),(850,true),(854,false),(858,true),(866,true)]
theorem inp_12404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 26) (closed_mem 23 26) cl_12404 (by decide) v hb
def cl_12405 : CNF.NClause := [(837,true),(846,true),(850,false),(854,true),(858,true),(866,true)]
theorem inp_12405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 26) (closed_mem 23 26) cl_12405 (by decide) v hb
def cl_12406 : CNF.NClause := [(837,true),(846,false),(850,true),(854,true),(858,true),(866,true)]
theorem inp_12406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 26) (closed_mem 23 26) cl_12406 (by decide) v hb
def cl_12409 : CNF.NClause := [(837,true),(844,true),(851,true),(853,true),(860,false),(864,true)]
theorem inp_12409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 27) (closed_mem 23 27) cl_12409 (by decide) v hb
def cl_12414 : CNF.NClause := [(837,true),(845,true),(848,true),(856,true),(859,true),(865,false)]
theorem inp_12414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 28) (closed_mem 23 28) cl_12414 (by decide) v hb
def cl_12415 : CNF.NClause := [(837,true),(845,true),(848,true),(856,true),(859,false),(865,true)]
theorem inp_12415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 28) (closed_mem 23 28) cl_12415 (by decide) v hb
def cl_12418 : CNF.NClause := [(837,true),(845,false),(848,true),(856,true),(859,true),(865,true)]
theorem inp_12418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 28) (closed_mem 23 28) cl_12418 (by decide) v hb
def cl_12420 : CNF.NClause := [(837,true),(843,true),(849,true),(855,true),(861,true),(863,false)]
theorem inp_12420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 29) (closed_mem 23 29) cl_12420 (by decide) v hb
end Percolation.NReplay
