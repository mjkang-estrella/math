import NInputs220
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14455 : CNF.NClause := [(22,true),(30,true),(836,false)]
theorem inp_14455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14455 v hb
def cl_14456 : CNF.NClause := [(23,true),(0,true),(837,false)]
theorem inp_14456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14456 = (containClause5 23 0) := by decide
  rw [he]
  exact input_contain 23 0 (by decide) v hb
def cl_14457 : CNF.NClause := [(23,true),(1,true),(838,false)]
theorem inp_14457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14457 = (containClause5 23 1) := by decide
  rw [he]
  exact input_contain 23 1 (by decide) v hb
def cl_14458 : CNF.NClause := [(23,true),(2,true),(839,false)]
theorem inp_14458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14458 = (containClause5 23 2) := by decide
  rw [he]
  exact input_contain 23 2 (by decide) v hb
def cl_14459 : CNF.NClause := [(23,true),(3,true),(840,false)]
theorem inp_14459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14459 = (containClause5 23 3) := by decide
  rw [he]
  exact input_contain 23 3 (by decide) v hb
def cl_14460 : CNF.NClause := [(23,true),(4,true),(841,false)]
theorem inp_14460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14460 = (containClause5 23 4) := by decide
  rw [he]
  exact input_contain 23 4 (by decide) v hb
def cl_14461 : CNF.NClause := [(23,true),(5,true),(842,false)]
theorem inp_14461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14461 = (containClause5 23 5) := by decide
  rw [he]
  exact input_contain 23 5 (by decide) v hb
def cl_14462 : CNF.NClause := [(23,true),(6,true),(843,false)]
theorem inp_14462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14462 = (containClause5 23 6) := by decide
  rw [he]
  exact input_contain 23 6 (by decide) v hb
def cl_14463 : CNF.NClause := [(23,true),(7,true),(844,false)]
theorem inp_14463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14463 = (containClause5 23 7) := by decide
  rw [he]
  exact input_contain 23 7 (by decide) v hb
def cl_14464 : CNF.NClause := [(23,true),(8,true),(845,false)]
theorem inp_14464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14464 = (containClause5 23 8) := by decide
  rw [he]
  exact input_contain 23 8 (by decide) v hb
def cl_14465 : CNF.NClause := [(23,true),(9,true),(846,false)]
theorem inp_14465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14465 = (containClause5 23 9) := by decide
  rw [he]
  exact input_contain 23 9 (by decide) v hb
def cl_14466 : CNF.NClause := [(23,true),(10,true),(847,false)]
theorem inp_14466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14466 = (containClause5 23 10) := by decide
  rw [he]
  exact input_contain 23 10 (by decide) v hb
def cl_14467 : CNF.NClause := [(23,true),(11,true),(848,false)]
theorem inp_14467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14467 = (containClause5 23 11) := by decide
  rw [he]
  exact input_contain 23 11 (by decide) v hb
def cl_14468 : CNF.NClause := [(23,true),(12,true),(849,false)]
theorem inp_14468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14468 = (containClause5 23 12) := by decide
  rw [he]
  exact input_contain 23 12 (by decide) v hb
def cl_14469 : CNF.NClause := [(23,true),(13,true),(850,false)]
theorem inp_14469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14469 = (containClause5 23 13) := by decide
  rw [he]
  exact input_contain 23 13 (by decide) v hb
def cl_14470 : CNF.NClause := [(23,true),(14,true),(851,false)]
theorem inp_14470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14470 = (containClause5 23 14) := by decide
  rw [he]
  exact input_contain 23 14 (by decide) v hb
def cl_14471 : CNF.NClause := [(23,true),(15,true),(852,false)]
theorem inp_14471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14471 = (containClause5 23 15) := by decide
  rw [he]
  exact input_contain 23 15 (by decide) v hb
def cl_14472 : CNF.NClause := [(23,true),(16,true),(853,false)]
theorem inp_14472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14472 = (containClause5 23 16) := by decide
  rw [he]
  exact input_contain 23 16 (by decide) v hb
def cl_14473 : CNF.NClause := [(23,true),(17,true),(854,false)]
theorem inp_14473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14473 = (containClause5 23 17) := by decide
  rw [he]
  exact input_contain 23 17 (by decide) v hb
def cl_14474 : CNF.NClause := [(23,true),(18,true),(855,false)]
theorem inp_14474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14474 = (containClause5 23 18) := by decide
  rw [he]
  exact input_contain 23 18 (by decide) v hb
def cl_14475 : CNF.NClause := [(23,true),(19,true),(856,false)]
theorem inp_14475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14475 = (containClause5 23 19) := by decide
  rw [he]
  exact input_contain 23 19 (by decide) v hb
def cl_14476 : CNF.NClause := [(23,true),(20,true),(857,false)]
theorem inp_14476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14476 = (containClause5 23 20) := by decide
  rw [he]
  exact input_contain 23 20 (by decide) v hb
def cl_14477 : CNF.NClause := [(23,true),(21,true),(858,false)]
theorem inp_14477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14477 = (containClause5 23 21) := by decide
  rw [he]
  exact input_contain 23 21 (by decide) v hb
def cl_14478 : CNF.NClause := [(23,true),(22,true),(859,false)]
theorem inp_14478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14478 = (containClause5 23 22) := by decide
  rw [he]
  exact input_contain 23 22 (by decide) v hb
def cl_14479 : CNF.NClause := [(23,true),(24,true),(861,false)]
theorem inp_14479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14479 = (containClause5 23 24) := by decide
  rw [he]
  exact input_contain 23 24 (by decide) v hb
def cl_14480 : CNF.NClause := [(23,true),(25,true),(862,false)]
theorem inp_14480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14480 = (containClause5 23 25) := by decide
  rw [he]
  exact input_contain 23 25 (by decide) v hb
def cl_14481 : CNF.NClause := [(23,true),(26,true),(863,false)]
theorem inp_14481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14481 = (containClause5 23 26) := by decide
  rw [he]
  exact input_contain 23 26 (by decide) v hb
def cl_14482 : CNF.NClause := [(23,true),(27,true),(864,false)]
theorem inp_14482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14482 = (containClause5 23 27) := by decide
  rw [he]
  exact input_contain 23 27 (by decide) v hb
def cl_14483 : CNF.NClause := [(23,true),(28,true),(865,false)]
theorem inp_14483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14483 = (containClause5 23 28) := by decide
  rw [he]
  exact input_contain 23 28 (by decide) v hb
def cl_14484 : CNF.NClause := [(23,true),(29,true),(866,false)]
theorem inp_14484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14484 = (containClause5 23 29) := by decide
  rw [he]
  exact input_contain 23 29 (by decide) v hb
def cl_14485 : CNF.NClause := [(23,true),(30,true),(867,false)]
theorem inp_14485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14485 = (containClause5 23 30) := by decide
  rw [he]
  exact input_contain 23 30 (by decide) v hb
def cl_14486 : CNF.NClause := [(24,true),(0,true),(868,false)]
theorem inp_14486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14486 = (containClause5 24 0) := by decide
  rw [he]
  exact input_contain 24 0 (by decide) v hb
def cl_14487 : CNF.NClause := [(24,true),(1,true),(869,false)]
theorem inp_14487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14487 = (containClause5 24 1) := by decide
  rw [he]
  exact input_contain 24 1 (by decide) v hb
def cl_14488 : CNF.NClause := [(24,true),(2,true),(870,false)]
theorem inp_14488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14488 = (containClause5 24 2) := by decide
  rw [he]
  exact input_contain 24 2 (by decide) v hb
def cl_14489 : CNF.NClause := [(24,true),(3,true),(871,false)]
theorem inp_14489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14489 = (containClause5 24 3) := by decide
  rw [he]
  exact input_contain 24 3 (by decide) v hb
def cl_14490 : CNF.NClause := [(24,true),(4,true),(872,false)]
theorem inp_14490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14490 = (containClause5 24 4) := by decide
  rw [he]
  exact input_contain 24 4 (by decide) v hb
def cl_14491 : CNF.NClause := [(24,true),(5,true),(873,false)]
theorem inp_14491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14491 = (containClause5 24 5) := by decide
  rw [he]
  exact input_contain 24 5 (by decide) v hb
def cl_14492 : CNF.NClause := [(24,true),(6,true),(874,false)]
theorem inp_14492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14492 = (containClause5 24 6) := by decide
  rw [he]
  exact input_contain 24 6 (by decide) v hb
def cl_14493 : CNF.NClause := [(24,true),(7,true),(875,false)]
theorem inp_14493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14493 = (containClause5 24 7) := by decide
  rw [he]
  exact input_contain 24 7 (by decide) v hb
def cl_14494 : CNF.NClause := [(24,true),(8,true),(876,false)]
theorem inp_14494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14494 = (containClause5 24 8) := by decide
  rw [he]
  exact input_contain 24 8 (by decide) v hb
def cl_14495 : CNF.NClause := [(24,true),(9,true),(877,false)]
theorem inp_14495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14495 = (containClause5 24 9) := by decide
  rw [he]
  exact input_contain 24 9 (by decide) v hb
def cl_14496 : CNF.NClause := [(24,true),(10,true),(878,false)]
theorem inp_14496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14496 = (containClause5 24 10) := by decide
  rw [he]
  exact input_contain 24 10 (by decide) v hb
def cl_14497 : CNF.NClause := [(24,true),(11,true),(879,false)]
theorem inp_14497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14497 = (containClause5 24 11) := by decide
  rw [he]
  exact input_contain 24 11 (by decide) v hb
def cl_14498 : CNF.NClause := [(24,true),(12,true),(880,false)]
theorem inp_14498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14498 = (containClause5 24 12) := by decide
  rw [he]
  exact input_contain 24 12 (by decide) v hb
def cl_14499 : CNF.NClause := [(24,true),(13,true),(881,false)]
theorem inp_14499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14499 = (containClause5 24 13) := by decide
  rw [he]
  exact input_contain 24 13 (by decide) v hb
def cl_14500 : CNF.NClause := [(24,true),(14,true),(882,false)]
theorem inp_14500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14500 = (containClause5 24 14) := by decide
  rw [he]
  exact input_contain 24 14 (by decide) v hb
def cl_14501 : CNF.NClause := [(24,true),(15,true),(883,false)]
theorem inp_14501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14501 = (containClause5 24 15) := by decide
  rw [he]
  exact input_contain 24 15 (by decide) v hb
def cl_14502 : CNF.NClause := [(24,true),(16,true),(884,false)]
theorem inp_14502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14502 = (containClause5 24 16) := by decide
  rw [he]
  exact input_contain 24 16 (by decide) v hb
def cl_14503 : CNF.NClause := [(24,true),(17,true),(885,false)]
theorem inp_14503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14503 = (containClause5 24 17) := by decide
  rw [he]
  exact input_contain 24 17 (by decide) v hb
def cl_14504 : CNF.NClause := [(24,true),(18,true),(886,false)]
theorem inp_14504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14504 = (containClause5 24 18) := by decide
  rw [he]
  exact input_contain 24 18 (by decide) v hb
end Percolation.NReplay
