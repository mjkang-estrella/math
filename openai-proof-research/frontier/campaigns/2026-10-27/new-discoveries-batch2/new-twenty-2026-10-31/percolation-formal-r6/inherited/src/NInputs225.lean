import NInputs224
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14655 : CNF.NClause := [(29,true),(19,true),(1042,false)]
theorem inp_14655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14655 = (containClause5 29 19) := by decide
  rw [he]
  exact input_contain 29 19 (by decide) v hb
def cl_14656 : CNF.NClause := [(29,true),(20,true),(1043,false)]
theorem inp_14656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14656 = (containClause5 29 20) := by decide
  rw [he]
  exact input_contain 29 20 (by decide) v hb
def cl_14657 : CNF.NClause := [(29,true),(21,true),(1044,false)]
theorem inp_14657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14657 = (containClause5 29 21) := by decide
  rw [he]
  exact input_contain 29 21 (by decide) v hb
def cl_14658 : CNF.NClause := [(29,true),(22,true),(1045,false)]
theorem inp_14658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14658 = (containClause5 29 22) := by decide
  rw [he]
  exact input_contain 29 22 (by decide) v hb
def cl_14659 : CNF.NClause := [(29,true),(23,true),(1046,false)]
theorem inp_14659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14659 = (containClause5 29 23) := by decide
  rw [he]
  exact input_contain 29 23 (by decide) v hb
def cl_14660 : CNF.NClause := [(29,true),(24,true),(1047,false)]
theorem inp_14660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14660 = (containClause5 29 24) := by decide
  rw [he]
  exact input_contain 29 24 (by decide) v hb
def cl_14661 : CNF.NClause := [(29,true),(25,true),(1048,false)]
theorem inp_14661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14661 = (containClause5 29 25) := by decide
  rw [he]
  exact input_contain 29 25 (by decide) v hb
def cl_14662 : CNF.NClause := [(29,true),(26,true),(1049,false)]
theorem inp_14662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14662 = (containClause5 29 26) := by decide
  rw [he]
  exact input_contain 29 26 (by decide) v hb
def cl_14663 : CNF.NClause := [(29,true),(27,true),(1050,false)]
theorem inp_14663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14663 = (containClause5 29 27) := by decide
  rw [he]
  exact input_contain 29 27 (by decide) v hb
def cl_14664 : CNF.NClause := [(29,true),(28,true),(1051,false)]
theorem inp_14664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14664 = (containClause5 29 28) := by decide
  rw [he]
  exact input_contain 29 28 (by decide) v hb
def cl_14665 : CNF.NClause := [(29,true),(30,true),(1053,false)]
theorem inp_14665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14665 = (containClause5 29 30) := by decide
  rw [he]
  exact input_contain 29 30 (by decide) v hb
def cl_14666 : CNF.NClause := [(30,true),(0,true),(1054,false)]
theorem inp_14666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14666 v hb
def cl_14667 : CNF.NClause := [(30,true),(1,true),(1055,false)]
theorem inp_14667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14667 v hb
def cl_14668 : CNF.NClause := [(30,true),(2,true),(1056,false)]
theorem inp_14668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14668 v hb
def cl_14669 : CNF.NClause := [(30,true),(3,true),(1057,false)]
theorem inp_14669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14669 v hb
def cl_14670 : CNF.NClause := [(30,true),(4,true),(1058,false)]
theorem inp_14670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14670 v hb
def cl_14671 : CNF.NClause := [(30,true),(5,true),(1059,false)]
theorem inp_14671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14671 v hb
def cl_14672 : CNF.NClause := [(30,true),(6,true),(1060,false)]
theorem inp_14672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14672 v hb
def cl_14673 : CNF.NClause := [(30,true),(7,true),(1061,false)]
theorem inp_14673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14673 = (containClause5 30 7) := by decide
  rw [he]
  exact input_contain 30 7 (by decide) v hb
def cl_14674 : CNF.NClause := [(30,true),(8,true),(1062,false)]
theorem inp_14674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14674 v hb
def cl_14675 : CNF.NClause := [(30,true),(9,true),(1063,false)]
theorem inp_14675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14675 v hb
def cl_14676 : CNF.NClause := [(30,true),(10,true),(1064,false)]
theorem inp_14676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14676 v hb
def cl_14677 : CNF.NClause := [(30,true),(11,true),(1065,false)]
theorem inp_14677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14677 v hb
def cl_14678 : CNF.NClause := [(30,true),(12,true),(1066,false)]
theorem inp_14678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14678 v hb
def cl_14679 : CNF.NClause := [(30,true),(13,true),(1067,false)]
theorem inp_14679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14679 = (containClause5 30 13) := by decide
  rw [he]
  exact input_contain 30 13 (by decide) v hb
def cl_14680 : CNF.NClause := [(30,true),(14,true),(1068,false)]
theorem inp_14680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14680 = (containClause5 30 14) := by decide
  rw [he]
  exact input_contain 30 14 (by decide) v hb
def cl_14681 : CNF.NClause := [(30,true),(15,true),(1069,false)]
theorem inp_14681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14681 = (containClause5 30 15) := by decide
  rw [he]
  exact input_contain 30 15 (by decide) v hb
def cl_14682 : CNF.NClause := [(30,true),(16,true),(1070,false)]
theorem inp_14682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14682 = (containClause5 30 16) := by decide
  rw [he]
  exact input_contain 30 16 (by decide) v hb
def cl_14683 : CNF.NClause := [(30,true),(17,true),(1071,false)]
theorem inp_14683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14683 v hb
def cl_14684 : CNF.NClause := [(30,true),(18,true),(1072,false)]
theorem inp_14684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14684 v hb
def cl_14685 : CNF.NClause := [(30,true),(19,true),(1073,false)]
theorem inp_14685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14685 v hb
def cl_14686 : CNF.NClause := [(30,true),(20,true),(1074,false)]
theorem inp_14686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14686 = (containClause5 30 20) := by decide
  rw [he]
  exact input_contain 30 20 (by decide) v hb
def cl_14687 : CNF.NClause := [(30,true),(21,true),(1075,false)]
theorem inp_14687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14687 = (containClause5 30 21) := by decide
  rw [he]
  exact input_contain 30 21 (by decide) v hb
def cl_14688 : CNF.NClause := [(30,true),(22,true),(1076,false)]
theorem inp_14688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14688 = (containClause5 30 22) := by decide
  rw [he]
  exact input_contain 30 22 (by decide) v hb
def cl_14689 : CNF.NClause := [(30,true),(23,true),(1077,false)]
theorem inp_14689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14689 v hb
def cl_14690 : CNF.NClause := [(30,true),(24,true),(1078,false)]
theorem inp_14690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14690 v hb
def cl_14691 : CNF.NClause := [(30,true),(25,true),(1079,false)]
theorem inp_14691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14691 v hb
def cl_14692 : CNF.NClause := [(30,true),(26,true),(1080,false)]
theorem inp_14692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14692 v hb
def cl_14693 : CNF.NClause := [(30,true),(27,true),(1081,false)]
theorem inp_14693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14693 v hb
def cl_14694 : CNF.NClause := [(30,true),(28,true),(1082,false)]
theorem inp_14694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14694 = (containClause5 30 28) := by decide
  rw [he]
  exact input_contain 30 28 (by decide) v hb
def cl_14695 : CNF.NClause := [(30,true),(29,true),(1083,false)]
theorem inp_14695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14695 = (containClause5 30 29) := by decide
  rw [he]
  exact input_contain 30 29 (by decide) v hb
def cl_14696 : CNF.NClause := [(0,false)]
theorem inp_14696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14696 := by
  apply holds_decode
  apply h
  exact List.mem_append_right _ (by decide : decodeClause cl_14696 ∈ normalizedUnits5)
def cl_14697 : CNF.NClause := [(25,false)]
theorem inp_14697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14697 := by
  apply holds_decode
  apply h
  exact List.mem_append_right _ (by decide : decodeClause cl_14697 ∈ normalizedUnits5)
def cl_14698 : CNF.NClause := [(30,false)]
theorem inp_14698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14698 := by
  apply holds_decode
  apply h
  exact List.mem_append_right _ (by decide : decodeClause cl_14698 ∈ normalizedUnits5)
end Percolation.NReplay
