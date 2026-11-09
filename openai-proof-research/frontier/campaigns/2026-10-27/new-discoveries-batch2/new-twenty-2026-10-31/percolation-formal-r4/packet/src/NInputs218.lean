import NInputs217
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14305 : CNF.NClause := [(17,true),(30,true),(681,false)]
theorem inp_14305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14305 v hb
def cl_14306 : CNF.NClause := [(18,true),(0,true),(682,false)]
theorem inp_14306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14306 = (containClause5 18 0) := by decide
  rw [he]
  exact input_contain 18 0 (by decide) v hb
def cl_14307 : CNF.NClause := [(18,true),(1,true),(683,false)]
theorem inp_14307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14307 = (containClause5 18 1) := by decide
  rw [he]
  exact input_contain 18 1 (by decide) v hb
def cl_14308 : CNF.NClause := [(18,true),(2,true),(684,false)]
theorem inp_14308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14308 v hb
def cl_14309 : CNF.NClause := [(18,true),(3,true),(685,false)]
theorem inp_14309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14309 = (containClause5 18 3) := by decide
  rw [he]
  exact input_contain 18 3 (by decide) v hb
def cl_14310 : CNF.NClause := [(18,true),(4,true),(686,false)]
theorem inp_14310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14310 = (containClause5 18 4) := by decide
  rw [he]
  exact input_contain 18 4 (by decide) v hb
def cl_14311 : CNF.NClause := [(18,true),(5,true),(687,false)]
theorem inp_14311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14311 = (containClause5 18 5) := by decide
  rw [he]
  exact input_contain 18 5 (by decide) v hb
def cl_14312 : CNF.NClause := [(18,true),(6,true),(688,false)]
theorem inp_14312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14312 v hb
def cl_14313 : CNF.NClause := [(18,true),(7,true),(689,false)]
theorem inp_14313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14313 = (containClause5 18 7) := by decide
  rw [he]
  exact input_contain 18 7 (by decide) v hb
def cl_14314 : CNF.NClause := [(18,true),(8,true),(690,false)]
theorem inp_14314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14314 = (containClause5 18 8) := by decide
  rw [he]
  exact input_contain 18 8 (by decide) v hb
def cl_14315 : CNF.NClause := [(18,true),(9,true),(691,false)]
theorem inp_14315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14315 = (containClause5 18 9) := by decide
  rw [he]
  exact input_contain 18 9 (by decide) v hb
def cl_14316 : CNF.NClause := [(18,true),(10,true),(692,false)]
theorem inp_14316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14316 v hb
def cl_14317 : CNF.NClause := [(18,true),(11,true),(693,false)]
theorem inp_14317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14317 = (containClause5 18 11) := by decide
  rw [he]
  exact input_contain 18 11 (by decide) v hb
def cl_14318 : CNF.NClause := [(18,true),(12,true),(694,false)]
theorem inp_14318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14318 = (containClause5 18 12) := by decide
  rw [he]
  exact input_contain 18 12 (by decide) v hb
def cl_14319 : CNF.NClause := [(18,true),(13,true),(695,false)]
theorem inp_14319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14319 = (containClause5 18 13) := by decide
  rw [he]
  exact input_contain 18 13 (by decide) v hb
def cl_14320 : CNF.NClause := [(18,true),(14,true),(696,false)]
theorem inp_14320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14320 = (containClause5 18 14) := by decide
  rw [he]
  exact input_contain 18 14 (by decide) v hb
def cl_14321 : CNF.NClause := [(18,true),(15,true),(697,false)]
theorem inp_14321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14321 = (containClause5 18 15) := by decide
  rw [he]
  exact input_contain 18 15 (by decide) v hb
def cl_14322 : CNF.NClause := [(18,true),(16,true),(698,false)]
theorem inp_14322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14322 = (containClause5 18 16) := by decide
  rw [he]
  exact input_contain 18 16 (by decide) v hb
def cl_14323 : CNF.NClause := [(18,true),(17,true),(699,false)]
theorem inp_14323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14323 = (containClause5 18 17) := by decide
  rw [he]
  exact input_contain 18 17 (by decide) v hb
def cl_14324 : CNF.NClause := [(18,true),(19,true),(701,false)]
theorem inp_14324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14324 = (containClause5 18 19) := by decide
  rw [he]
  exact input_contain 18 19 (by decide) v hb
def cl_14325 : CNF.NClause := [(18,true),(20,true),(702,false)]
theorem inp_14325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14325 = (containClause5 18 20) := by decide
  rw [he]
  exact input_contain 18 20 (by decide) v hb
def cl_14326 : CNF.NClause := [(18,true),(21,true),(703,false)]
theorem inp_14326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14326 = (containClause5 18 21) := by decide
  rw [he]
  exact input_contain 18 21 (by decide) v hb
def cl_14327 : CNF.NClause := [(18,true),(22,true),(704,false)]
theorem inp_14327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14327 = (containClause5 18 22) := by decide
  rw [he]
  exact input_contain 18 22 (by decide) v hb
def cl_14328 : CNF.NClause := [(18,true),(23,true),(705,false)]
theorem inp_14328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14328 v hb
def cl_14329 : CNF.NClause := [(18,true),(24,true),(706,false)]
theorem inp_14329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14329 = (containClause5 18 24) := by decide
  rw [he]
  exact input_contain 18 24 (by decide) v hb
def cl_14330 : CNF.NClause := [(18,true),(25,true),(707,false)]
theorem inp_14330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14330 = (containClause5 18 25) := by decide
  rw [he]
  exact input_contain 18 25 (by decide) v hb
def cl_14331 : CNF.NClause := [(18,true),(26,true),(708,false)]
theorem inp_14331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14331 = (containClause5 18 26) := by decide
  rw [he]
  exact input_contain 18 26 (by decide) v hb
def cl_14332 : CNF.NClause := [(18,true),(27,true),(709,false)]
theorem inp_14332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14332 = (containClause5 18 27) := by decide
  rw [he]
  exact input_contain 18 27 (by decide) v hb
def cl_14333 : CNF.NClause := [(18,true),(28,true),(710,false)]
theorem inp_14333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14333 = (containClause5 18 28) := by decide
  rw [he]
  exact input_contain 18 28 (by decide) v hb
def cl_14334 : CNF.NClause := [(18,true),(29,true),(711,false)]
theorem inp_14334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14334 = (containClause5 18 29) := by decide
  rw [he]
  exact input_contain 18 29 (by decide) v hb
def cl_14335 : CNF.NClause := [(18,true),(30,true),(712,false)]
theorem inp_14335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14335 = (containClause5 18 30) := by decide
  rw [he]
  exact input_contain 18 30 (by decide) v hb
def cl_14336 : CNF.NClause := [(19,true),(0,true),(713,false)]
theorem inp_14336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14336 = (containClause5 19 0) := by decide
  rw [he]
  exact input_contain 19 0 (by decide) v hb
def cl_14337 : CNF.NClause := [(19,true),(1,true),(714,false)]
theorem inp_14337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14337 = (containClause5 19 1) := by decide
  rw [he]
  exact input_contain 19 1 (by decide) v hb
def cl_14338 : CNF.NClause := [(19,true),(2,true),(715,false)]
theorem inp_14338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14338 = (containClause5 19 2) := by decide
  rw [he]
  exact input_contain 19 2 (by decide) v hb
def cl_14339 : CNF.NClause := [(19,true),(3,true),(716,false)]
theorem inp_14339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14339 = (containClause5 19 3) := by decide
  rw [he]
  exact input_contain 19 3 (by decide) v hb
def cl_14340 : CNF.NClause := [(19,true),(4,true),(717,false)]
theorem inp_14340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14340 v hb
def cl_14341 : CNF.NClause := [(19,true),(5,true),(718,false)]
theorem inp_14341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14341 = (containClause5 19 5) := by decide
  rw [he]
  exact input_contain 19 5 (by decide) v hb
def cl_14342 : CNF.NClause := [(19,true),(6,true),(719,false)]
theorem inp_14342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14342 = (containClause5 19 6) := by decide
  rw [he]
  exact input_contain 19 6 (by decide) v hb
def cl_14343 : CNF.NClause := [(19,true),(7,true),(720,false)]
theorem inp_14343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14343 v hb
def cl_14344 : CNF.NClause := [(19,true),(8,true),(721,false)]
theorem inp_14344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14344 = (containClause5 19 8) := by decide
  rw [he]
  exact input_contain 19 8 (by decide) v hb
def cl_14345 : CNF.NClause := [(19,true),(9,true),(722,false)]
theorem inp_14345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14345 v hb
def cl_14346 : CNF.NClause := [(19,true),(10,true),(723,false)]
theorem inp_14346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14346 = (containClause5 19 10) := by decide
  rw [he]
  exact input_contain 19 10 (by decide) v hb
def cl_14347 : CNF.NClause := [(19,true),(11,true),(724,false)]
theorem inp_14347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14347 = (containClause5 19 11) := by decide
  rw [he]
  exact input_contain 19 11 (by decide) v hb
def cl_14348 : CNF.NClause := [(19,true),(12,true),(725,false)]
theorem inp_14348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14348 = (containClause5 19 12) := by decide
  rw [he]
  exact input_contain 19 12 (by decide) v hb
def cl_14349 : CNF.NClause := [(19,true),(13,true),(726,false)]
theorem inp_14349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14349 = (containClause5 19 13) := by decide
  rw [he]
  exact input_contain 19 13 (by decide) v hb
def cl_14350 : CNF.NClause := [(19,true),(14,true),(727,false)]
theorem inp_14350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14350 v hb
def cl_14351 : CNF.NClause := [(19,true),(15,true),(728,false)]
theorem inp_14351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14351 = (containClause5 19 15) := by decide
  rw [he]
  exact input_contain 19 15 (by decide) v hb
def cl_14352 : CNF.NClause := [(19,true),(16,true),(729,false)]
theorem inp_14352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14352 v hb
def cl_14353 : CNF.NClause := [(19,true),(17,true),(730,false)]
theorem inp_14353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14353 = (containClause5 19 17) := by decide
  rw [he]
  exact input_contain 19 17 (by decide) v hb
def cl_14354 : CNF.NClause := [(19,true),(18,true),(731,false)]
theorem inp_14354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14354 = (containClause5 19 18) := by decide
  rw [he]
  exact input_contain 19 18 (by decide) v hb
end Percolation.NReplay
