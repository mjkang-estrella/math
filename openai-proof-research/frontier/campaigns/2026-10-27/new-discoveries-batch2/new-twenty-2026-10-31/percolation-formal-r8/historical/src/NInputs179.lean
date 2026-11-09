import NInputs178
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11331 : CNF.NClause := [(684,true),(689,true),(694,false),(699,true),(704,true),(707,true)]
theorem inp_11331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 2) (closed_mem 18 2) cl_11331 (by decide) v hb
def cl_11332 : CNF.NClause := [(684,true),(689,false),(694,true),(699,true),(704,true),(707,true)]
theorem inp_11332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 2) (closed_mem 18 2) cl_11332 (by decide) v hb
def cl_11333 : CNF.NClause := [(684,false),(689,true),(694,true),(699,true),(704,true),(707,true)]
theorem inp_11333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 2) (closed_mem 18 2) cl_11333 (by decide) v hb
def cl_11336 : CNF.NClause := [(685,true),(690,true),(695,true),(700,false),(705,true),(707,true)]
theorem inp_11336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 3) (closed_mem 18 3) cl_11336 (by decide) v hb
def cl_11341 : CNF.NClause := [(683,true),(688,true),(693,true),(698,true),(703,false),(707,true)]
theorem inp_11341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11341 v hb
def cl_11342 : CNF.NClause := [(683,true),(688,true),(693,true),(698,false),(703,true),(707,true)]
theorem inp_11342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 4) (closed_mem 18 4) cl_11342 (by decide) v hb
def cl_11343 : CNF.NClause := [(683,true),(688,true),(693,false),(698,true),(703,true),(707,true)]
theorem inp_11343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 4) (closed_mem 18 4) cl_11343 (by decide) v hb
def cl_11344 : CNF.NClause := [(683,true),(688,false),(693,true),(698,true),(703,true),(707,true)]
theorem inp_11344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 4) (closed_mem 18 4) cl_11344 (by decide) v hb
def cl_11345 : CNF.NClause := [(683,false),(688,true),(693,true),(698,true),(703,true),(707,true)]
theorem inp_11345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 4) (closed_mem 18 4) cl_11345 (by decide) v hb
def cl_11347 : CNF.NClause := [(702,true),(703,true),(704,true),(705,true),(706,false),(712,true)]
theorem inp_11347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 5) (closed_mem 18 5) cl_11347 (by decide) v hb
def cl_11348 : CNF.NClause := [(702,true),(703,true),(704,true),(705,false),(706,true),(712,true)]
theorem inp_11348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 5) (closed_mem 18 5) cl_11348 (by decide) v hb
def cl_11349 : CNF.NClause := [(702,true),(703,true),(704,false),(705,true),(706,true),(712,true)]
theorem inp_11349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 5) (closed_mem 18 5) cl_11349 (by decide) v hb
def cl_11350 : CNF.NClause := [(702,true),(703,false),(704,true),(705,true),(706,true),(712,true)]
theorem inp_11350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 5) (closed_mem 18 5) cl_11350 (by decide) v hb
def cl_11351 : CNF.NClause := [(702,false),(703,true),(704,true),(705,true),(706,true),(712,true)]
theorem inp_11351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 5) (closed_mem 18 5) cl_11351 (by decide) v hb
def cl_11352 : CNF.NClause := [(686,true),(690,true),(694,true),(698,true),(702,true),(711,false)]
theorem inp_11352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 6) (closed_mem 18 6) cl_11352 (by decide) v hb
def cl_11353 : CNF.NClause := [(686,true),(690,true),(694,true),(698,true),(702,false),(711,true)]
theorem inp_11353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 6) (closed_mem 18 6) cl_11353 (by decide) v hb
def cl_11355 : CNF.NClause := [(686,true),(690,true),(694,false),(698,true),(702,true),(711,true)]
theorem inp_11355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 6) (closed_mem 18 6) cl_11355 (by decide) v hb
def cl_11356 : CNF.NClause := [(686,true),(690,false),(694,true),(698,true),(702,true),(711,true)]
theorem inp_11356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 6) (closed_mem 18 6) cl_11356 (by decide) v hb
def cl_11360 : CNF.NClause := [(684,true),(691,true),(693,true),(700,false),(702,true),(709,true)]
theorem inp_11360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 7) (closed_mem 18 7) cl_11360 (by decide) v hb
def cl_11364 : CNF.NClause := [(685,true),(688,true),(696,true),(699,true),(702,true),(710,false)]
theorem inp_11364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 8) (closed_mem 18 8) cl_11364 (by decide) v hb
def cl_11365 : CNF.NClause := [(685,true),(688,true),(696,true),(699,true),(702,false),(710,true)]
theorem inp_11365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 8) (closed_mem 18 8) cl_11365 (by decide) v hb
def cl_11366 : CNF.NClause := [(685,true),(688,true),(696,true),(699,false),(702,true),(710,true)]
theorem inp_11366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 8) (closed_mem 18 8) cl_11366 (by decide) v hb
def cl_11367 : CNF.NClause := [(685,true),(688,true),(696,false),(699,true),(702,true),(710,true)]
theorem inp_11367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 8) (closed_mem 18 8) cl_11367 (by decide) v hb
def cl_11368 : CNF.NClause := [(685,true),(688,false),(696,true),(699,true),(702,true),(710,true)]
theorem inp_11368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 8) (closed_mem 18 8) cl_11368 (by decide) v hb
def cl_11369 : CNF.NClause := [(685,false),(688,true),(696,true),(699,true),(702,true),(710,true)]
theorem inp_11369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 8) (closed_mem 18 8) cl_11369 (by decide) v hb
def cl_11371 : CNF.NClause := [(683,true),(689,true),(695,true),(701,true),(702,false),(708,true)]
theorem inp_11371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 9) (closed_mem 18 9) cl_11371 (by decide) v hb
def cl_11372 : CNF.NClause := [(683,true),(689,true),(695,true),(701,false),(702,true),(708,true)]
theorem inp_11372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 9) (closed_mem 18 9) cl_11372 (by decide) v hb
def cl_11373 : CNF.NClause := [(683,true),(689,true),(695,false),(701,true),(702,true),(708,true)]
theorem inp_11373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 9) (closed_mem 18 9) cl_11373 (by decide) v hb
def cl_11374 : CNF.NClause := [(683,true),(689,false),(695,true),(701,true),(702,true),(708,true)]
theorem inp_11374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11374 v hb
def cl_11375 : CNF.NClause := [(683,false),(689,true),(695,true),(701,true),(702,true),(708,true)]
theorem inp_11375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 9) (closed_mem 18 9) cl_11375 (by decide) v hb
def cl_11377 : CNF.NClause := [(692,true),(693,true),(694,true),(695,true),(696,false),(712,true)]
theorem inp_11377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 10) (closed_mem 18 10) cl_11377 (by decide) v hb
def cl_11378 : CNF.NClause := [(692,true),(693,true),(694,true),(695,false),(696,true),(712,true)]
theorem inp_11378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 10) (closed_mem 18 10) cl_11378 (by decide) v hb
def cl_11379 : CNF.NClause := [(692,true),(693,true),(694,false),(695,true),(696,true),(712,true)]
theorem inp_11379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 10) (closed_mem 18 10) cl_11379 (by decide) v hb
def cl_11380 : CNF.NClause := [(692,true),(693,false),(694,true),(695,true),(696,true),(712,true)]
theorem inp_11380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 10) (closed_mem 18 10) cl_11380 (by decide) v hb
def cl_11381 : CNF.NClause := [(692,false),(693,true),(694,true),(695,true),(696,true),(712,true)]
theorem inp_11381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 10) (closed_mem 18 10) cl_11381 (by decide) v hb
def cl_11384 : CNF.NClause := [(686,true),(689,true),(692,true),(700,false),(703,true),(710,true)]
theorem inp_11384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11384 v hb
def cl_11389 : CNF.NClause := [(684,true),(688,true),(692,true),(701,true),(705,false),(711,true)]
theorem inp_11389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 12) (closed_mem 18 12) cl_11389 (by decide) v hb
def cl_11391 : CNF.NClause := [(684,true),(688,true),(692,false),(701,true),(705,true),(711,true)]
theorem inp_11391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 12) (closed_mem 18 12) cl_11391 (by decide) v hb
def cl_11392 : CNF.NClause := [(684,true),(688,false),(692,true),(701,true),(705,true),(711,true)]
theorem inp_11392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 12) (closed_mem 18 12) cl_11392 (by decide) v hb
def cl_11393 : CNF.NClause := [(684,false),(688,true),(692,true),(701,true),(705,true),(711,true)]
theorem inp_11393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11393 v hb
def cl_11394 : CNF.NClause := [(685,true),(691,true),(692,true),(698,true),(704,true),(708,false)]
theorem inp_11394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 13) (closed_mem 18 13) cl_11394 (by decide) v hb
def cl_11395 : CNF.NClause := [(685,true),(691,true),(692,true),(698,true),(704,false),(708,true)]
theorem inp_11395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 13) (closed_mem 18 13) cl_11395 (by decide) v hb
def cl_11396 : CNF.NClause := [(685,true),(691,true),(692,true),(698,false),(704,true),(708,true)]
theorem inp_11396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 13) (closed_mem 18 13) cl_11396 (by decide) v hb
def cl_11397 : CNF.NClause := [(685,true),(691,true),(692,false),(698,true),(704,true),(708,true)]
theorem inp_11397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 13) (closed_mem 18 13) cl_11397 (by decide) v hb
def cl_11399 : CNF.NClause := [(685,false),(691,true),(692,true),(698,true),(704,true),(708,true)]
theorem inp_11399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 13) (closed_mem 18 13) cl_11399 (by decide) v hb
def cl_11400 : CNF.NClause := [(683,true),(690,true),(692,true),(699,true),(706,true),(709,false)]
theorem inp_11400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 14) (closed_mem 18 14) cl_11400 (by decide) v hb
def cl_11404 : CNF.NClause := [(683,true),(690,false),(692,true),(699,true),(706,true),(709,true)]
theorem inp_11404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 14) (closed_mem 18 14) cl_11404 (by decide) v hb
def cl_11405 : CNF.NClause := [(683,false),(690,true),(692,true),(699,true),(706,true),(709,true)]
theorem inp_11405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 14) (closed_mem 18 14) cl_11405 (by decide) v hb
def cl_11408 : CNF.NClause := [(697,true),(698,true),(699,true),(700,false),(701,true),(712,true)]
theorem inp_11408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 15) (closed_mem 18 15) cl_11408 (by decide) v hb
def cl_11412 : CNF.NClause := [(686,true),(688,true),(695,true),(697,true),(704,true),(709,false)]
theorem inp_11412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 16) (closed_mem 18 16) cl_11412 (by decide) v hb
end Percolation.NReplay
