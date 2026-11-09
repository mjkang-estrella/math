import NInputs218
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14355 : CNF.NClause := [(19,true),(20,true),(733,false)]
theorem inp_14355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14355 = (containClause5 19 20) := by decide
  rw [he]
  exact input_contain 19 20 (by decide) v hb
def cl_14356 : CNF.NClause := [(19,true),(21,true),(734,false)]
theorem inp_14356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14356 = (containClause5 19 21) := by decide
  rw [he]
  exact input_contain 19 21 (by decide) v hb
def cl_14357 : CNF.NClause := [(19,true),(22,true),(735,false)]
theorem inp_14357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14357 = (containClause5 19 22) := by decide
  rw [he]
  exact input_contain 19 22 (by decide) v hb
def cl_14358 : CNF.NClause := [(19,true),(23,true),(736,false)]
theorem inp_14358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14358 v hb
def cl_14359 : CNF.NClause := [(19,true),(24,true),(737,false)]
theorem inp_14359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14359 v hb
def cl_14360 : CNF.NClause := [(19,true),(25,true),(738,false)]
theorem inp_14360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14360 = (containClause5 19 25) := by decide
  rw [he]
  exact input_contain 19 25 (by decide) v hb
def cl_14361 : CNF.NClause := [(19,true),(26,true),(739,false)]
theorem inp_14361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14361 = (containClause5 19 26) := by decide
  rw [he]
  exact input_contain 19 26 (by decide) v hb
def cl_14362 : CNF.NClause := [(19,true),(27,true),(740,false)]
theorem inp_14362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14362 v hb
def cl_14363 : CNF.NClause := [(19,true),(28,true),(741,false)]
theorem inp_14363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14363 = (containClause5 19 28) := by decide
  rw [he]
  exact input_contain 19 28 (by decide) v hb
def cl_14364 : CNF.NClause := [(19,true),(29,true),(742,false)]
theorem inp_14364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14364 = (containClause5 19 29) := by decide
  rw [he]
  exact input_contain 19 29 (by decide) v hb
def cl_14365 : CNF.NClause := [(19,true),(30,true),(743,false)]
theorem inp_14365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14365 = (containClause5 19 30) := by decide
  rw [he]
  exact input_contain 19 30 (by decide) v hb
def cl_14366 : CNF.NClause := [(20,true),(0,true),(744,false)]
theorem inp_14366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14366 = (containClause5 20 0) := by decide
  rw [he]
  exact input_contain 20 0 (by decide) v hb
def cl_14367 : CNF.NClause := [(20,true),(1,true),(745,false)]
theorem inp_14367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14367 = (containClause5 20 1) := by decide
  rw [he]
  exact input_contain 20 1 (by decide) v hb
def cl_14368 : CNF.NClause := [(20,true),(2,true),(746,false)]
theorem inp_14368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14368 = (containClause5 20 2) := by decide
  rw [he]
  exact input_contain 20 2 (by decide) v hb
def cl_14369 : CNF.NClause := [(20,true),(3,true),(747,false)]
theorem inp_14369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14369 = (containClause5 20 3) := by decide
  rw [he]
  exact input_contain 20 3 (by decide) v hb
def cl_14370 : CNF.NClause := [(20,true),(4,true),(748,false)]
theorem inp_14370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14370 = (containClause5 20 4) := by decide
  rw [he]
  exact input_contain 20 4 (by decide) v hb
def cl_14371 : CNF.NClause := [(20,true),(5,true),(749,false)]
theorem inp_14371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14371 = (containClause5 20 5) := by decide
  rw [he]
  exact input_contain 20 5 (by decide) v hb
def cl_14372 : CNF.NClause := [(20,true),(6,true),(750,false)]
theorem inp_14372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14372 = (containClause5 20 6) := by decide
  rw [he]
  exact input_contain 20 6 (by decide) v hb
def cl_14373 : CNF.NClause := [(20,true),(7,true),(751,false)]
theorem inp_14373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14373 = (containClause5 20 7) := by decide
  rw [he]
  exact input_contain 20 7 (by decide) v hb
def cl_14374 : CNF.NClause := [(20,true),(8,true),(752,false)]
theorem inp_14374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14374 = (containClause5 20 8) := by decide
  rw [he]
  exact input_contain 20 8 (by decide) v hb
def cl_14375 : CNF.NClause := [(20,true),(9,true),(753,false)]
theorem inp_14375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14375 = (containClause5 20 9) := by decide
  rw [he]
  exact input_contain 20 9 (by decide) v hb
def cl_14376 : CNF.NClause := [(20,true),(10,true),(754,false)]
theorem inp_14376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14376 = (containClause5 20 10) := by decide
  rw [he]
  exact input_contain 20 10 (by decide) v hb
def cl_14377 : CNF.NClause := [(20,true),(11,true),(755,false)]
theorem inp_14377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14377 = (containClause5 20 11) := by decide
  rw [he]
  exact input_contain 20 11 (by decide) v hb
def cl_14378 : CNF.NClause := [(20,true),(12,true),(756,false)]
theorem inp_14378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14378 = (containClause5 20 12) := by decide
  rw [he]
  exact input_contain 20 12 (by decide) v hb
def cl_14379 : CNF.NClause := [(20,true),(13,true),(757,false)]
theorem inp_14379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14379 = (containClause5 20 13) := by decide
  rw [he]
  exact input_contain 20 13 (by decide) v hb
def cl_14380 : CNF.NClause := [(20,true),(14,true),(758,false)]
theorem inp_14380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14380 = (containClause5 20 14) := by decide
  rw [he]
  exact input_contain 20 14 (by decide) v hb
def cl_14381 : CNF.NClause := [(20,true),(15,true),(759,false)]
theorem inp_14381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14381 = (containClause5 20 15) := by decide
  rw [he]
  exact input_contain 20 15 (by decide) v hb
def cl_14382 : CNF.NClause := [(20,true),(16,true),(760,false)]
theorem inp_14382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14382 = (containClause5 20 16) := by decide
  rw [he]
  exact input_contain 20 16 (by decide) v hb
def cl_14383 : CNF.NClause := [(20,true),(17,true),(761,false)]
theorem inp_14383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14383 = (containClause5 20 17) := by decide
  rw [he]
  exact input_contain 20 17 (by decide) v hb
def cl_14384 : CNF.NClause := [(20,true),(18,true),(762,false)]
theorem inp_14384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14384 = (containClause5 20 18) := by decide
  rw [he]
  exact input_contain 20 18 (by decide) v hb
def cl_14385 : CNF.NClause := [(20,true),(19,true),(763,false)]
theorem inp_14385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14385 = (containClause5 20 19) := by decide
  rw [he]
  exact input_contain 20 19 (by decide) v hb
def cl_14386 : CNF.NClause := [(20,true),(21,true),(765,false)]
theorem inp_14386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14386 = (containClause5 20 21) := by decide
  rw [he]
  exact input_contain 20 21 (by decide) v hb
def cl_14387 : CNF.NClause := [(20,true),(22,true),(766,false)]
theorem inp_14387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14387 = (containClause5 20 22) := by decide
  rw [he]
  exact input_contain 20 22 (by decide) v hb
def cl_14388 : CNF.NClause := [(20,true),(23,true),(767,false)]
theorem inp_14388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14388 = (containClause5 20 23) := by decide
  rw [he]
  exact input_contain 20 23 (by decide) v hb
def cl_14389 : CNF.NClause := [(20,true),(24,true),(768,false)]
theorem inp_14389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14389 = (containClause5 20 24) := by decide
  rw [he]
  exact input_contain 20 24 (by decide) v hb
def cl_14390 : CNF.NClause := [(20,true),(25,true),(769,false)]
theorem inp_14390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14390 = (containClause5 20 25) := by decide
  rw [he]
  exact input_contain 20 25 (by decide) v hb
def cl_14391 : CNF.NClause := [(20,true),(26,true),(770,false)]
theorem inp_14391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14391 = (containClause5 20 26) := by decide
  rw [he]
  exact input_contain 20 26 (by decide) v hb
def cl_14392 : CNF.NClause := [(20,true),(27,true),(771,false)]
theorem inp_14392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14392 = (containClause5 20 27) := by decide
  rw [he]
  exact input_contain 20 27 (by decide) v hb
def cl_14393 : CNF.NClause := [(20,true),(28,true),(772,false)]
theorem inp_14393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14393 = (containClause5 20 28) := by decide
  rw [he]
  exact input_contain 20 28 (by decide) v hb
def cl_14394 : CNF.NClause := [(20,true),(29,true),(773,false)]
theorem inp_14394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14394 = (containClause5 20 29) := by decide
  rw [he]
  exact input_contain 20 29 (by decide) v hb
def cl_14395 : CNF.NClause := [(20,true),(30,true),(774,false)]
theorem inp_14395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14395 = (containClause5 20 30) := by decide
  rw [he]
  exact input_contain 20 30 (by decide) v hb
def cl_14396 : CNF.NClause := [(21,true),(0,true),(775,false)]
theorem inp_14396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14396 v hb
def cl_14397 : CNF.NClause := [(21,true),(1,true),(776,false)]
theorem inp_14397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14397 v hb
def cl_14398 : CNF.NClause := [(21,true),(2,true),(777,false)]
theorem inp_14398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14398 v hb
def cl_14399 : CNF.NClause := [(21,true),(3,true),(778,false)]
theorem inp_14399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14399 = (containClause5 21 3) := by decide
  rw [he]
  exact input_contain 21 3 (by decide) v hb
def cl_14400 : CNF.NClause := [(21,true),(4,true),(779,false)]
theorem inp_14400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14400 = (containClause5 21 4) := by decide
  rw [he]
  exact input_contain 21 4 (by decide) v hb
def cl_14401 : CNF.NClause := [(21,true),(5,true),(780,false)]
theorem inp_14401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14401 v hb
def cl_14402 : CNF.NClause := [(21,true),(6,true),(781,false)]
theorem inp_14402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14402 = (containClause5 21 6) := by decide
  rw [he]
  exact input_contain 21 6 (by decide) v hb
def cl_14403 : CNF.NClause := [(21,true),(7,true),(782,false)]
theorem inp_14403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14403 = (containClause5 21 7) := by decide
  rw [he]
  exact input_contain 21 7 (by decide) v hb
def cl_14404 : CNF.NClause := [(21,true),(8,true),(783,false)]
theorem inp_14404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14404 = (containClause5 21 8) := by decide
  rw [he]
  exact input_contain 21 8 (by decide) v hb
end Percolation.NReplay
