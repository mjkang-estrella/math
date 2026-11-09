import NInputs223
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14605 : CNF.NClause := [(27,true),(30,true),(991,false)]
theorem inp_14605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14605 = (containClause5 27 30) := by decide
  rw [he]
  exact input_contain 27 30 (by decide) v hb
def cl_14606 : CNF.NClause := [(28,true),(0,true),(992,false)]
theorem inp_14606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14606 v hb
def cl_14607 : CNF.NClause := [(28,true),(1,true),(993,false)]
theorem inp_14607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14607 = (containClause5 28 1) := by decide
  rw [he]
  exact input_contain 28 1 (by decide) v hb
def cl_14608 : CNF.NClause := [(28,true),(2,true),(994,false)]
theorem inp_14608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14608 = (containClause5 28 2) := by decide
  rw [he]
  exact input_contain 28 2 (by decide) v hb
def cl_14609 : CNF.NClause := [(28,true),(3,true),(995,false)]
theorem inp_14609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14609 = (containClause5 28 3) := by decide
  rw [he]
  exact input_contain 28 3 (by decide) v hb
def cl_14610 : CNF.NClause := [(28,true),(4,true),(996,false)]
theorem inp_14610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14610 = (containClause5 28 4) := by decide
  rw [he]
  exact input_contain 28 4 (by decide) v hb
def cl_14611 : CNF.NClause := [(28,true),(5,true),(997,false)]
theorem inp_14611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14611 v hb
def cl_14612 : CNF.NClause := [(28,true),(6,true),(998,false)]
theorem inp_14612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14612 = (containClause5 28 6) := by decide
  rw [he]
  exact input_contain 28 6 (by decide) v hb
def cl_14613 : CNF.NClause := [(28,true),(7,true),(999,false)]
theorem inp_14613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14613 = (containClause5 28 7) := by decide
  rw [he]
  exact input_contain 28 7 (by decide) v hb
def cl_14614 : CNF.NClause := [(28,true),(8,true),(1000,false)]
theorem inp_14614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14614 = (containClause5 28 8) := by decide
  rw [he]
  exact input_contain 28 8 (by decide) v hb
def cl_14615 : CNF.NClause := [(28,true),(9,true),(1001,false)]
theorem inp_14615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14615 = (containClause5 28 9) := by decide
  rw [he]
  exact input_contain 28 9 (by decide) v hb
def cl_14616 : CNF.NClause := [(28,true),(10,true),(1002,false)]
theorem inp_14616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14616 v hb
def cl_14617 : CNF.NClause := [(28,true),(11,true),(1003,false)]
theorem inp_14617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14617 = (containClause5 28 11) := by decide
  rw [he]
  exact input_contain 28 11 (by decide) v hb
def cl_14618 : CNF.NClause := [(28,true),(12,true),(1004,false)]
theorem inp_14618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14618 = (containClause5 28 12) := by decide
  rw [he]
  exact input_contain 28 12 (by decide) v hb
def cl_14619 : CNF.NClause := [(28,true),(13,true),(1005,false)]
theorem inp_14619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14619 = (containClause5 28 13) := by decide
  rw [he]
  exact input_contain 28 13 (by decide) v hb
def cl_14620 : CNF.NClause := [(28,true),(14,true),(1006,false)]
theorem inp_14620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14620 = (containClause5 28 14) := by decide
  rw [he]
  exact input_contain 28 14 (by decide) v hb
def cl_14621 : CNF.NClause := [(28,true),(15,true),(1007,false)]
theorem inp_14621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14621 v hb
def cl_14622 : CNF.NClause := [(28,true),(16,true),(1008,false)]
theorem inp_14622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14622 = (containClause5 28 16) := by decide
  rw [he]
  exact input_contain 28 16 (by decide) v hb
def cl_14623 : CNF.NClause := [(28,true),(17,true),(1009,false)]
theorem inp_14623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14623 = (containClause5 28 17) := by decide
  rw [he]
  exact input_contain 28 17 (by decide) v hb
def cl_14624 : CNF.NClause := [(28,true),(18,true),(1010,false)]
theorem inp_14624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14624 = (containClause5 28 18) := by decide
  rw [he]
  exact input_contain 28 18 (by decide) v hb
def cl_14625 : CNF.NClause := [(28,true),(19,true),(1011,false)]
theorem inp_14625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14625 = (containClause5 28 19) := by decide
  rw [he]
  exact input_contain 28 19 (by decide) v hb
def cl_14626 : CNF.NClause := [(28,true),(20,true),(1012,false)]
theorem inp_14626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14626 v hb
def cl_14627 : CNF.NClause := [(28,true),(21,true),(1013,false)]
theorem inp_14627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14627 = (containClause5 28 21) := by decide
  rw [he]
  exact input_contain 28 21 (by decide) v hb
def cl_14628 : CNF.NClause := [(28,true),(22,true),(1014,false)]
theorem inp_14628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14628 = (containClause5 28 22) := by decide
  rw [he]
  exact input_contain 28 22 (by decide) v hb
def cl_14629 : CNF.NClause := [(28,true),(23,true),(1015,false)]
theorem inp_14629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14629 = (containClause5 28 23) := by decide
  rw [he]
  exact input_contain 28 23 (by decide) v hb
def cl_14630 : CNF.NClause := [(28,true),(24,true),(1016,false)]
theorem inp_14630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14630 = (containClause5 28 24) := by decide
  rw [he]
  exact input_contain 28 24 (by decide) v hb
def cl_14631 : CNF.NClause := [(28,true),(25,true),(1017,false)]
theorem inp_14631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14631 v hb
def cl_14632 : CNF.NClause := [(28,true),(26,true),(1018,false)]
theorem inp_14632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14632 = (containClause5 28 26) := by decide
  rw [he]
  exact input_contain 28 26 (by decide) v hb
def cl_14633 : CNF.NClause := [(28,true),(27,true),(1019,false)]
theorem inp_14633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14633 = (containClause5 28 27) := by decide
  rw [he]
  exact input_contain 28 27 (by decide) v hb
def cl_14634 : CNF.NClause := [(28,true),(29,true),(1021,false)]
theorem inp_14634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14634 = (containClause5 28 29) := by decide
  rw [he]
  exact input_contain 28 29 (by decide) v hb
def cl_14635 : CNF.NClause := [(28,true),(30,true),(1022,false)]
theorem inp_14635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14635 = (containClause5 28 30) := by decide
  rw [he]
  exact input_contain 28 30 (by decide) v hb
def cl_14636 : CNF.NClause := [(29,true),(0,true),(1023,false)]
theorem inp_14636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14636 = (containClause5 29 0) := by decide
  rw [he]
  exact input_contain 29 0 (by decide) v hb
def cl_14637 : CNF.NClause := [(29,true),(1,true),(1024,false)]
theorem inp_14637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14637 = (containClause5 29 1) := by decide
  rw [he]
  exact input_contain 29 1 (by decide) v hb
def cl_14638 : CNF.NClause := [(29,true),(2,true),(1025,false)]
theorem inp_14638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14638 = (containClause5 29 2) := by decide
  rw [he]
  exact input_contain 29 2 (by decide) v hb
def cl_14639 : CNF.NClause := [(29,true),(3,true),(1026,false)]
theorem inp_14639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14639 = (containClause5 29 3) := by decide
  rw [he]
  exact input_contain 29 3 (by decide) v hb
def cl_14640 : CNF.NClause := [(29,true),(4,true),(1027,false)]
theorem inp_14640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14640 = (containClause5 29 4) := by decide
  rw [he]
  exact input_contain 29 4 (by decide) v hb
def cl_14641 : CNF.NClause := [(29,true),(5,true),(1028,false)]
theorem inp_14641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14641 = (containClause5 29 5) := by decide
  rw [he]
  exact input_contain 29 5 (by decide) v hb
def cl_14642 : CNF.NClause := [(29,true),(6,true),(1029,false)]
theorem inp_14642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14642 = (containClause5 29 6) := by decide
  rw [he]
  exact input_contain 29 6 (by decide) v hb
def cl_14643 : CNF.NClause := [(29,true),(7,true),(1030,false)]
theorem inp_14643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14643 = (containClause5 29 7) := by decide
  rw [he]
  exact input_contain 29 7 (by decide) v hb
def cl_14644 : CNF.NClause := [(29,true),(8,true),(1031,false)]
theorem inp_14644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14644 = (containClause5 29 8) := by decide
  rw [he]
  exact input_contain 29 8 (by decide) v hb
def cl_14645 : CNF.NClause := [(29,true),(9,true),(1032,false)]
theorem inp_14645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14645 = (containClause5 29 9) := by decide
  rw [he]
  exact input_contain 29 9 (by decide) v hb
def cl_14646 : CNF.NClause := [(29,true),(10,true),(1033,false)]
theorem inp_14646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14646 = (containClause5 29 10) := by decide
  rw [he]
  exact input_contain 29 10 (by decide) v hb
def cl_14647 : CNF.NClause := [(29,true),(11,true),(1034,false)]
theorem inp_14647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14647 = (containClause5 29 11) := by decide
  rw [he]
  exact input_contain 29 11 (by decide) v hb
def cl_14648 : CNF.NClause := [(29,true),(12,true),(1035,false)]
theorem inp_14648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14648 = (containClause5 29 12) := by decide
  rw [he]
  exact input_contain 29 12 (by decide) v hb
def cl_14649 : CNF.NClause := [(29,true),(13,true),(1036,false)]
theorem inp_14649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14649 = (containClause5 29 13) := by decide
  rw [he]
  exact input_contain 29 13 (by decide) v hb
def cl_14650 : CNF.NClause := [(29,true),(14,true),(1037,false)]
theorem inp_14650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14650 = (containClause5 29 14) := by decide
  rw [he]
  exact input_contain 29 14 (by decide) v hb
def cl_14651 : CNF.NClause := [(29,true),(15,true),(1038,false)]
theorem inp_14651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14651 = (containClause5 29 15) := by decide
  rw [he]
  exact input_contain 29 15 (by decide) v hb
def cl_14652 : CNF.NClause := [(29,true),(16,true),(1039,false)]
theorem inp_14652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14652 = (containClause5 29 16) := by decide
  rw [he]
  exact input_contain 29 16 (by decide) v hb
def cl_14653 : CNF.NClause := [(29,true),(17,true),(1040,false)]
theorem inp_14653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14653 = (containClause5 29 17) := by decide
  rw [he]
  exact input_contain 29 17 (by decide) v hb
def cl_14654 : CNF.NClause := [(29,true),(18,true),(1041,false)]
theorem inp_14654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14654 = (containClause5 29 18) := by decide
  rw [he]
  exact input_contain 29 18 (by decide) v hb
end Percolation.NReplay
