import NInputs222
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14555 : CNF.NClause := [(26,true),(9,true),(939,false)]
theorem inp_14555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14555 = (containClause5 26 9) := by decide
  rw [he]
  exact input_contain 26 9 (by decide) v hb
def cl_14556 : CNF.NClause := [(26,true),(10,true),(940,false)]
theorem inp_14556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14556 = (containClause5 26 10) := by decide
  rw [he]
  exact input_contain 26 10 (by decide) v hb
def cl_14557 : CNF.NClause := [(26,true),(11,true),(941,false)]
theorem inp_14557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14557 = (containClause5 26 11) := by decide
  rw [he]
  exact input_contain 26 11 (by decide) v hb
def cl_14558 : CNF.NClause := [(26,true),(12,true),(942,false)]
theorem inp_14558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14558 = (containClause5 26 12) := by decide
  rw [he]
  exact input_contain 26 12 (by decide) v hb
def cl_14559 : CNF.NClause := [(26,true),(13,true),(943,false)]
theorem inp_14559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14559 = (containClause5 26 13) := by decide
  rw [he]
  exact input_contain 26 13 (by decide) v hb
def cl_14560 : CNF.NClause := [(26,true),(14,true),(944,false)]
theorem inp_14560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14560 = (containClause5 26 14) := by decide
  rw [he]
  exact input_contain 26 14 (by decide) v hb
def cl_14561 : CNF.NClause := [(26,true),(15,true),(945,false)]
theorem inp_14561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14561 = (containClause5 26 15) := by decide
  rw [he]
  exact input_contain 26 15 (by decide) v hb
def cl_14562 : CNF.NClause := [(26,true),(16,true),(946,false)]
theorem inp_14562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14562 = (containClause5 26 16) := by decide
  rw [he]
  exact input_contain 26 16 (by decide) v hb
def cl_14563 : CNF.NClause := [(26,true),(17,true),(947,false)]
theorem inp_14563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14563 = (containClause5 26 17) := by decide
  rw [he]
  exact input_contain 26 17 (by decide) v hb
def cl_14564 : CNF.NClause := [(26,true),(18,true),(948,false)]
theorem inp_14564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14564 = (containClause5 26 18) := by decide
  rw [he]
  exact input_contain 26 18 (by decide) v hb
def cl_14565 : CNF.NClause := [(26,true),(19,true),(949,false)]
theorem inp_14565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14565 = (containClause5 26 19) := by decide
  rw [he]
  exact input_contain 26 19 (by decide) v hb
def cl_14566 : CNF.NClause := [(26,true),(20,true),(950,false)]
theorem inp_14566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14566 = (containClause5 26 20) := by decide
  rw [he]
  exact input_contain 26 20 (by decide) v hb
def cl_14567 : CNF.NClause := [(26,true),(21,true),(951,false)]
theorem inp_14567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14567 = (containClause5 26 21) := by decide
  rw [he]
  exact input_contain 26 21 (by decide) v hb
def cl_14568 : CNF.NClause := [(26,true),(22,true),(952,false)]
theorem inp_14568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14568 = (containClause5 26 22) := by decide
  rw [he]
  exact input_contain 26 22 (by decide) v hb
def cl_14569 : CNF.NClause := [(26,true),(23,true),(953,false)]
theorem inp_14569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14569 = (containClause5 26 23) := by decide
  rw [he]
  exact input_contain 26 23 (by decide) v hb
def cl_14570 : CNF.NClause := [(26,true),(24,true),(954,false)]
theorem inp_14570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14570 = (containClause5 26 24) := by decide
  rw [he]
  exact input_contain 26 24 (by decide) v hb
def cl_14571 : CNF.NClause := [(26,true),(25,true),(955,false)]
theorem inp_14571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14571 = (containClause5 26 25) := by decide
  rw [he]
  exact input_contain 26 25 (by decide) v hb
def cl_14572 : CNF.NClause := [(26,true),(27,true),(957,false)]
theorem inp_14572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14572 = (containClause5 26 27) := by decide
  rw [he]
  exact input_contain 26 27 (by decide) v hb
def cl_14573 : CNF.NClause := [(26,true),(28,true),(958,false)]
theorem inp_14573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14573 = (containClause5 26 28) := by decide
  rw [he]
  exact input_contain 26 28 (by decide) v hb
def cl_14574 : CNF.NClause := [(26,true),(29,true),(959,false)]
theorem inp_14574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14574 = (containClause5 26 29) := by decide
  rw [he]
  exact input_contain 26 29 (by decide) v hb
def cl_14575 : CNF.NClause := [(26,true),(30,true),(960,false)]
theorem inp_14575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14575 = (containClause5 26 30) := by decide
  rw [he]
  exact input_contain 26 30 (by decide) v hb
def cl_14576 : CNF.NClause := [(27,true),(0,true),(961,false)]
theorem inp_14576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14576 = (containClause5 27 0) := by decide
  rw [he]
  exact input_contain 27 0 (by decide) v hb
def cl_14577 : CNF.NClause := [(27,true),(1,true),(962,false)]
theorem inp_14577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14577 = (containClause5 27 1) := by decide
  rw [he]
  exact input_contain 27 1 (by decide) v hb
def cl_14578 : CNF.NClause := [(27,true),(2,true),(963,false)]
theorem inp_14578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14578 v hb
def cl_14579 : CNF.NClause := [(27,true),(3,true),(964,false)]
theorem inp_14579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14579 = (containClause5 27 3) := by decide
  rw [he]
  exact input_contain 27 3 (by decide) v hb
def cl_14580 : CNF.NClause := [(27,true),(4,true),(965,false)]
theorem inp_14580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14580 = (containClause5 27 4) := by decide
  rw [he]
  exact input_contain 27 4 (by decide) v hb
def cl_14581 : CNF.NClause := [(27,true),(5,true),(966,false)]
theorem inp_14581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14581 = (containClause5 27 5) := by decide
  rw [he]
  exact input_contain 27 5 (by decide) v hb
def cl_14582 : CNF.NClause := [(27,true),(6,true),(967,false)]
theorem inp_14582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14582 = (containClause5 27 6) := by decide
  rw [he]
  exact input_contain 27 6 (by decide) v hb
def cl_14583 : CNF.NClause := [(27,true),(7,true),(968,false)]
theorem inp_14583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14583 = (containClause5 27 7) := by decide
  rw [he]
  exact input_contain 27 7 (by decide) v hb
def cl_14584 : CNF.NClause := [(27,true),(8,true),(969,false)]
theorem inp_14584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14584 v hb
def cl_14585 : CNF.NClause := [(27,true),(9,true),(970,false)]
theorem inp_14585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14585 = (containClause5 27 9) := by decide
  rw [he]
  exact input_contain 27 9 (by decide) v hb
def cl_14586 : CNF.NClause := [(27,true),(10,true),(971,false)]
theorem inp_14586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14586 = (containClause5 27 10) := by decide
  rw [he]
  exact input_contain 27 10 (by decide) v hb
def cl_14587 : CNF.NClause := [(27,true),(11,true),(972,false)]
theorem inp_14587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14587 = (containClause5 27 11) := by decide
  rw [he]
  exact input_contain 27 11 (by decide) v hb
def cl_14588 : CNF.NClause := [(27,true),(12,true),(973,false)]
theorem inp_14588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14588 = (containClause5 27 12) := by decide
  rw [he]
  exact input_contain 27 12 (by decide) v hb
def cl_14589 : CNF.NClause := [(27,true),(13,true),(974,false)]
theorem inp_14589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14589 = (containClause5 27 13) := by decide
  rw [he]
  exact input_contain 27 13 (by decide) v hb
def cl_14590 : CNF.NClause := [(27,true),(14,true),(975,false)]
theorem inp_14590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14590 v hb
def cl_14591 : CNF.NClause := [(27,true),(15,true),(976,false)]
theorem inp_14591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14591 = (containClause5 27 15) := by decide
  rw [he]
  exact input_contain 27 15 (by decide) v hb
def cl_14592 : CNF.NClause := [(27,true),(16,true),(977,false)]
theorem inp_14592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14592 = (containClause5 27 16) := by decide
  rw [he]
  exact input_contain 27 16 (by decide) v hb
def cl_14593 : CNF.NClause := [(27,true),(17,true),(978,false)]
theorem inp_14593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14593 = (containClause5 27 17) := by decide
  rw [he]
  exact input_contain 27 17 (by decide) v hb
def cl_14594 : CNF.NClause := [(27,true),(18,true),(979,false)]
theorem inp_14594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14594 = (containClause5 27 18) := by decide
  rw [he]
  exact input_contain 27 18 (by decide) v hb
def cl_14595 : CNF.NClause := [(27,true),(19,true),(980,false)]
theorem inp_14595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14595 = (containClause5 27 19) := by decide
  rw [he]
  exact input_contain 27 19 (by decide) v hb
def cl_14596 : CNF.NClause := [(27,true),(20,true),(981,false)]
theorem inp_14596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14596 = (containClause5 27 20) := by decide
  rw [he]
  exact input_contain 27 20 (by decide) v hb
def cl_14597 : CNF.NClause := [(27,true),(21,true),(982,false)]
theorem inp_14597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14597 v hb
def cl_14598 : CNF.NClause := [(27,true),(22,true),(983,false)]
theorem inp_14598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14598 = (containClause5 27 22) := by decide
  rw [he]
  exact input_contain 27 22 (by decide) v hb
def cl_14599 : CNF.NClause := [(27,true),(23,true),(984,false)]
theorem inp_14599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14599 = (containClause5 27 23) := by decide
  rw [he]
  exact input_contain 27 23 (by decide) v hb
def cl_14600 : CNF.NClause := [(27,true),(24,true),(985,false)]
theorem inp_14600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14600 = (containClause5 27 24) := by decide
  rw [he]
  exact input_contain 27 24 (by decide) v hb
def cl_14601 : CNF.NClause := [(27,true),(25,true),(986,false)]
theorem inp_14601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14601 = (containClause5 27 25) := by decide
  rw [he]
  exact input_contain 27 25 (by decide) v hb
def cl_14602 : CNF.NClause := [(27,true),(26,true),(987,false)]
theorem inp_14602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14602 v hb
def cl_14603 : CNF.NClause := [(27,true),(28,true),(989,false)]
theorem inp_14603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14603 = (containClause5 27 28) := by decide
  rw [he]
  exact input_contain 27 28 (by decide) v hb
def cl_14604 : CNF.NClause := [(27,true),(29,true),(990,false)]
theorem inp_14604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14604 = (containClause5 27 29) := by decide
  rw [he]
  exact input_contain 27 29 (by decide) v hb
end Percolation.NReplay
