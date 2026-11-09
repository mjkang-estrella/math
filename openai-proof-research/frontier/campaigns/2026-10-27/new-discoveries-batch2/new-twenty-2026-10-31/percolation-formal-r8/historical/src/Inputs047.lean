import Inputs046
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14621 : CNF.NClause := [(28,true),(15,true),(1007,false)]
theorem inp_14621 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14621 := by
  apply holds_decode v cl_14621
  have he : decodeClause cl_14621 = containClause5 28 15 := by decide
  rw [he]
  exact input_contain 28 15 (by decide) v h
def cl_14626 : CNF.NClause := [(28,true),(20,true),(1012,false)]
theorem inp_14626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14626 := by
  apply holds_decode v cl_14626
  have he : decodeClause cl_14626 = containClause5 28 20 := by decide
  rw [he]
  exact input_contain 28 20 (by decide) v h
def cl_14631 : CNF.NClause := [(28,true),(25,true),(1017,false)]
theorem inp_14631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14631 := by
  apply holds_decode v cl_14631
  have he : decodeClause cl_14631 = containClause5 28 25 := by decide
  rw [he]
  exact input_contain 28 25 (by decide) v h
def cl_14666 : CNF.NClause := [(30,true),(0,true),(1054,false)]
theorem inp_14666 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14666 := by
  apply holds_decode v cl_14666
  have he : decodeClause cl_14666 = containClause5 30 0 := by decide
  rw [he]
  exact input_contain 30 0 (by decide) v h
def cl_14667 : CNF.NClause := [(30,true),(1,true),(1055,false)]
theorem inp_14667 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14667 := by
  apply holds_decode v cl_14667
  have he : decodeClause cl_14667 = containClause5 30 1 := by decide
  rw [he]
  exact input_contain 30 1 (by decide) v h
def cl_14668 : CNF.NClause := [(30,true),(2,true),(1056,false)]
theorem inp_14668 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14668 := by
  apply holds_decode v cl_14668
  have he : decodeClause cl_14668 = containClause5 30 2 := by decide
  rw [he]
  exact input_contain 30 2 (by decide) v h
def cl_14669 : CNF.NClause := [(30,true),(3,true),(1057,false)]
theorem inp_14669 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14669 := by
  apply holds_decode v cl_14669
  have he : decodeClause cl_14669 = containClause5 30 3 := by decide
  rw [he]
  exact input_contain 30 3 (by decide) v h
def cl_14670 : CNF.NClause := [(30,true),(4,true),(1058,false)]
theorem inp_14670 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14670 := by
  apply holds_decode v cl_14670
  have he : decodeClause cl_14670 = containClause5 30 4 := by decide
  rw [he]
  exact input_contain 30 4 (by decide) v h
def cl_14671 : CNF.NClause := [(30,true),(5,true),(1059,false)]
theorem inp_14671 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14671 := by
  apply holds_decode v cl_14671
  have he : decodeClause cl_14671 = containClause5 30 5 := by decide
  rw [he]
  exact input_contain 30 5 (by decide) v h
def cl_14672 : CNF.NClause := [(30,true),(6,true),(1060,false)]
theorem inp_14672 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14672 := by
  apply holds_decode v cl_14672
  have he : decodeClause cl_14672 = containClause5 30 6 := by decide
  rw [he]
  exact input_contain 30 6 (by decide) v h
def cl_14674 : CNF.NClause := [(30,true),(8,true),(1062,false)]
theorem inp_14674 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14674 := by
  apply holds_decode v cl_14674
  have he : decodeClause cl_14674 = containClause5 30 8 := by decide
  rw [he]
  exact input_contain 30 8 (by decide) v h
def cl_14675 : CNF.NClause := [(30,true),(9,true),(1063,false)]
theorem inp_14675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14675 := by
  apply holds_decode v cl_14675
  have he : decodeClause cl_14675 = containClause5 30 9 := by decide
  rw [he]
  exact input_contain 30 9 (by decide) v h
def cl_14676 : CNF.NClause := [(30,true),(10,true),(1064,false)]
theorem inp_14676 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14676 := by
  apply holds_decode v cl_14676
  have he : decodeClause cl_14676 = containClause5 30 10 := by decide
  rw [he]
  exact input_contain 30 10 (by decide) v h
def cl_14677 : CNF.NClause := [(30,true),(11,true),(1065,false)]
theorem inp_14677 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14677 := by
  apply holds_decode v cl_14677
  have he : decodeClause cl_14677 = containClause5 30 11 := by decide
  rw [he]
  exact input_contain 30 11 (by decide) v h
def cl_14678 : CNF.NClause := [(30,true),(12,true),(1066,false)]
theorem inp_14678 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14678 := by
  apply holds_decode v cl_14678
  have he : decodeClause cl_14678 = containClause5 30 12 := by decide
  rw [he]
  exact input_contain 30 12 (by decide) v h
def cl_14683 : CNF.NClause := [(30,true),(17,true),(1071,false)]
theorem inp_14683 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14683 := by
  apply holds_decode v cl_14683
  have he : decodeClause cl_14683 = containClause5 30 17 := by decide
  rw [he]
  exact input_contain 30 17 (by decide) v h
def cl_14684 : CNF.NClause := [(30,true),(18,true),(1072,false)]
theorem inp_14684 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14684 := by
  apply holds_decode v cl_14684
  have he : decodeClause cl_14684 = containClause5 30 18 := by decide
  rw [he]
  exact input_contain 30 18 (by decide) v h
def cl_14685 : CNF.NClause := [(30,true),(19,true),(1073,false)]
theorem inp_14685 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14685 := by
  apply holds_decode v cl_14685
  have he : decodeClause cl_14685 = containClause5 30 19 := by decide
  rw [he]
  exact input_contain 30 19 (by decide) v h
def cl_14689 : CNF.NClause := [(30,true),(23,true),(1077,false)]
theorem inp_14689 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14689 := by
  apply holds_decode v cl_14689
  have he : decodeClause cl_14689 = containClause5 30 23 := by decide
  rw [he]
  exact input_contain 30 23 (by decide) v h
def cl_14690 : CNF.NClause := [(30,true),(24,true),(1078,false)]
theorem inp_14690 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14690 := by
  apply holds_decode v cl_14690
  have he : decodeClause cl_14690 = containClause5 30 24 := by decide
  rw [he]
  exact input_contain 30 24 (by decide) v h
def cl_14691 : CNF.NClause := [(30,true),(25,true),(1079,false)]
theorem inp_14691 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14691 := by
  apply holds_decode v cl_14691
  have he : decodeClause cl_14691 = containClause5 30 25 := by decide
  rw [he]
  exact input_contain 30 25 (by decide) v h
def cl_14692 : CNF.NClause := [(30,true),(26,true),(1080,false)]
theorem inp_14692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14692 := by
  apply holds_decode v cl_14692
  have he : decodeClause cl_14692 = containClause5 30 26 := by decide
  rw [he]
  exact input_contain 30 26 (by decide) v h
def cl_14693 : CNF.NClause := [(30,true),(27,true),(1081,false)]
theorem inp_14693 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14693 := by
  apply holds_decode v cl_14693
  have he : decodeClause cl_14693 = containClause5 30 27 := by decide
  rw [he]
  exact input_contain 30 27 (by decide) v h
end Percolation.Replay
