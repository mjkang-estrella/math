import Inputs044
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14065 : CNF.NClause := [(9,true),(30,true),(433,false)]
theorem inp_14065 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14065 := by
  apply holds_decode v cl_14065
  have he : decodeClause cl_14065 = containClause5 9 30 := by decide
  rw [he]
  exact input_contain 9 30 (by decide) v h
def cl_14066 : CNF.NClause := [(10,true),(0,true),(434,false)]
theorem inp_14066 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14066 := by
  apply holds_decode v cl_14066
  have he : decodeClause cl_14066 = containClause5 10 0 := by decide
  rw [he]
  exact input_contain 10 0 (by decide) v h
def cl_14067 : CNF.NClause := [(10,true),(1,true),(435,false)]
theorem inp_14067 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14067 := by
  apply holds_decode v cl_14067
  have he : decodeClause cl_14067 = containClause5 10 1 := by decide
  rw [he]
  exact input_contain 10 1 (by decide) v h
def cl_14068 : CNF.NClause := [(10,true),(2,true),(436,false)]
theorem inp_14068 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14068 := by
  apply holds_decode v cl_14068
  have he : decodeClause cl_14068 = containClause5 10 2 := by decide
  rw [he]
  exact input_contain 10 2 (by decide) v h
def cl_14069 : CNF.NClause := [(10,true),(3,true),(437,false)]
theorem inp_14069 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14069 := by
  apply holds_decode v cl_14069
  have he : decodeClause cl_14069 = containClause5 10 3 := by decide
  rw [he]
  exact input_contain 10 3 (by decide) v h
def cl_14070 : CNF.NClause := [(10,true),(4,true),(438,false)]
theorem inp_14070 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14070 := by
  apply holds_decode v cl_14070
  have he : decodeClause cl_14070 = containClause5 10 4 := by decide
  rw [he]
  exact input_contain 10 4 (by decide) v h
def cl_14072 : CNF.NClause := [(10,true),(6,true),(440,false)]
theorem inp_14072 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14072 := by
  apply holds_decode v cl_14072
  have he : decodeClause cl_14072 = containClause5 10 6 := by decide
  rw [he]
  exact input_contain 10 6 (by decide) v h
def cl_14073 : CNF.NClause := [(10,true),(7,true),(441,false)]
theorem inp_14073 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14073 := by
  apply holds_decode v cl_14073
  have he : decodeClause cl_14073 = containClause5 10 7 := by decide
  rw [he]
  exact input_contain 10 7 (by decide) v h
def cl_14074 : CNF.NClause := [(10,true),(8,true),(442,false)]
theorem inp_14074 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14074 := by
  apply holds_decode v cl_14074
  have he : decodeClause cl_14074 = containClause5 10 8 := by decide
  rw [he]
  exact input_contain 10 8 (by decide) v h
def cl_14075 : CNF.NClause := [(10,true),(9,true),(443,false)]
theorem inp_14075 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14075 := by
  apply holds_decode v cl_14075
  have he : decodeClause cl_14075 = containClause5 10 9 := by decide
  rw [he]
  exact input_contain 10 9 (by decide) v h
def cl_14076 : CNF.NClause := [(10,true),(11,true),(445,false)]
theorem inp_14076 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14076 := by
  apply holds_decode v cl_14076
  have he : decodeClause cl_14076 = containClause5 10 11 := by decide
  rw [he]
  exact input_contain 10 11 (by decide) v h
def cl_14077 : CNF.NClause := [(10,true),(12,true),(446,false)]
theorem inp_14077 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14077 := by
  apply holds_decode v cl_14077
  have he : decodeClause cl_14077 = containClause5 10 12 := by decide
  rw [he]
  exact input_contain 10 12 (by decide) v h
def cl_14078 : CNF.NClause := [(10,true),(13,true),(447,false)]
theorem inp_14078 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14078 := by
  apply holds_decode v cl_14078
  have he : decodeClause cl_14078 = containClause5 10 13 := by decide
  rw [he]
  exact input_contain 10 13 (by decide) v h
def cl_14079 : CNF.NClause := [(10,true),(14,true),(448,false)]
theorem inp_14079 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14079 := by
  apply holds_decode v cl_14079
  have he : decodeClause cl_14079 = containClause5 10 14 := by decide
  rw [he]
  exact input_contain 10 14 (by decide) v h
def cl_14080 : CNF.NClause := [(10,true),(15,true),(449,false)]
theorem inp_14080 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14080 := by
  apply holds_decode v cl_14080
  have he : decodeClause cl_14080 = containClause5 10 15 := by decide
  rw [he]
  exact input_contain 10 15 (by decide) v h
def cl_14081 : CNF.NClause := [(10,true),(16,true),(450,false)]
theorem inp_14081 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14081 := by
  apply holds_decode v cl_14081
  have he : decodeClause cl_14081 = containClause5 10 16 := by decide
  rw [he]
  exact input_contain 10 16 (by decide) v h
def cl_14082 : CNF.NClause := [(10,true),(17,true),(451,false)]
theorem inp_14082 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14082 := by
  apply holds_decode v cl_14082
  have he : decodeClause cl_14082 = containClause5 10 17 := by decide
  rw [he]
  exact input_contain 10 17 (by decide) v h
def cl_14084 : CNF.NClause := [(10,true),(19,true),(453,false)]
theorem inp_14084 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14084 := by
  apply holds_decode v cl_14084
  have he : decodeClause cl_14084 = containClause5 10 19 := by decide
  rw [he]
  exact input_contain 10 19 (by decide) v h
def cl_14085 : CNF.NClause := [(10,true),(20,true),(454,false)]
theorem inp_14085 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14085 := by
  apply holds_decode v cl_14085
  have he : decodeClause cl_14085 = containClause5 10 20 := by decide
  rw [he]
  exact input_contain 10 20 (by decide) v h
def cl_14086 : CNF.NClause := [(10,true),(21,true),(455,false)]
theorem inp_14086 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14086 := by
  apply holds_decode v cl_14086
  have he : decodeClause cl_14086 = containClause5 10 21 := by decide
  rw [he]
  exact input_contain 10 21 (by decide) v h
def cl_14088 : CNF.NClause := [(10,true),(23,true),(457,false)]
theorem inp_14088 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14088 := by
  apply holds_decode v cl_14088
  have he : decodeClause cl_14088 = containClause5 10 23 := by decide
  rw [he]
  exact input_contain 10 23 (by decide) v h
def cl_14089 : CNF.NClause := [(10,true),(24,true),(458,false)]
theorem inp_14089 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14089 := by
  apply holds_decode v cl_14089
  have he : decodeClause cl_14089 = containClause5 10 24 := by decide
  rw [he]
  exact input_contain 10 24 (by decide) v h
def cl_14091 : CNF.NClause := [(10,true),(26,true),(460,false)]
theorem inp_14091 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14091 := by
  apply holds_decode v cl_14091
  have he : decodeClause cl_14091 = containClause5 10 26 := by decide
  rw [he]
  exact input_contain 10 26 (by decide) v h
def cl_14092 : CNF.NClause := [(10,true),(27,true),(461,false)]
theorem inp_14092 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14092 := by
  apply holds_decode v cl_14092
  have he : decodeClause cl_14092 = containClause5 10 27 := by decide
  rw [he]
  exact input_contain 10 27 (by decide) v h
def cl_14093 : CNF.NClause := [(10,true),(28,true),(462,false)]
theorem inp_14093 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14093 := by
  apply holds_decode v cl_14093
  have he : decodeClause cl_14093 = containClause5 10 28 := by decide
  rw [he]
  exact input_contain 10 28 (by decide) v h
def cl_14094 : CNF.NClause := [(10,true),(29,true),(463,false)]
theorem inp_14094 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14094 := by
  apply holds_decode v cl_14094
  have he : decodeClause cl_14094 = containClause5 10 29 := by decide
  rw [he]
  exact input_contain 10 29 (by decide) v h
def cl_14095 : CNF.NClause := [(10,true),(30,true),(464,false)]
theorem inp_14095 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14095 := by
  apply holds_decode v cl_14095
  have he : decodeClause cl_14095 = containClause5 10 30 := by decide
  rw [he]
  exact input_contain 10 30 (by decide) v h
def cl_14098 : CNF.NClause := [(11,true),(2,true),(467,false)]
theorem inp_14098 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14098 := by
  apply holds_decode v cl_14098
  have he : decodeClause cl_14098 = containClause5 11 2 := by decide
  rw [he]
  exact input_contain 11 2 (by decide) v h
def cl_14099 : CNF.NClause := [(11,true),(3,true),(468,false)]
theorem inp_14099 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14099 := by
  apply holds_decode v cl_14099
  have he : decodeClause cl_14099 = containClause5 11 3 := by decide
  rw [he]
  exact input_contain 11 3 (by decide) v h
def cl_14100 : CNF.NClause := [(11,true),(4,true),(469,false)]
theorem inp_14100 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14100 := by
  apply holds_decode v cl_14100
  have he : decodeClause cl_14100 = containClause5 11 4 := by decide
  rw [he]
  exact input_contain 11 4 (by decide) v h
def cl_14101 : CNF.NClause := [(11,true),(5,true),(470,false)]
theorem inp_14101 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14101 := by
  apply holds_decode v cl_14101
  have he : decodeClause cl_14101 = containClause5 11 5 := by decide
  rw [he]
  exact input_contain 11 5 (by decide) v h
def cl_14103 : CNF.NClause := [(11,true),(7,true),(472,false)]
theorem inp_14103 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14103 := by
  apply holds_decode v cl_14103
  have he : decodeClause cl_14103 = containClause5 11 7 := by decide
  rw [he]
  exact input_contain 11 7 (by decide) v h
def cl_14105 : CNF.NClause := [(11,true),(9,true),(474,false)]
theorem inp_14105 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14105 := by
  apply holds_decode v cl_14105
  have he : decodeClause cl_14105 = containClause5 11 9 := by decide
  rw [he]
  exact input_contain 11 9 (by decide) v h
def cl_14106 : CNF.NClause := [(11,true),(10,true),(475,false)]
theorem inp_14106 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14106 := by
  apply holds_decode v cl_14106
  have he : decodeClause cl_14106 = containClause5 11 10 := by decide
  rw [he]
  exact input_contain 11 10 (by decide) v h
def cl_14107 : CNF.NClause := [(11,true),(12,true),(477,false)]
theorem inp_14107 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14107 := by
  apply holds_decode v cl_14107
  have he : decodeClause cl_14107 = containClause5 11 12 := by decide
  rw [he]
  exact input_contain 11 12 (by decide) v h
def cl_14108 : CNF.NClause := [(11,true),(13,true),(478,false)]
theorem inp_14108 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14108 := by
  apply holds_decode v cl_14108
  have he : decodeClause cl_14108 = containClause5 11 13 := by decide
  rw [he]
  exact input_contain 11 13 (by decide) v h
def cl_14109 : CNF.NClause := [(11,true),(14,true),(479,false)]
theorem inp_14109 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14109 := by
  apply holds_decode v cl_14109
  have he : decodeClause cl_14109 = containClause5 11 14 := by decide
  rw [he]
  exact input_contain 11 14 (by decide) v h
def cl_14110 : CNF.NClause := [(11,true),(15,true),(480,false)]
theorem inp_14110 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14110 := by
  apply holds_decode v cl_14110
  have he : decodeClause cl_14110 = containClause5 11 15 := by decide
  rw [he]
  exact input_contain 11 15 (by decide) v h
def cl_14111 : CNF.NClause := [(11,true),(16,true),(481,false)]
theorem inp_14111 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14111 := by
  apply holds_decode v cl_14111
  have he : decodeClause cl_14111 = containClause5 11 16 := by decide
  rw [he]
  exact input_contain 11 16 (by decide) v h
def cl_14113 : CNF.NClause := [(11,true),(18,true),(483,false)]
theorem inp_14113 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14113 := by
  apply holds_decode v cl_14113
  have he : decodeClause cl_14113 = containClause5 11 18 := by decide
  rw [he]
  exact input_contain 11 18 (by decide) v h
def cl_14114 : CNF.NClause := [(11,true),(19,true),(484,false)]
theorem inp_14114 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14114 := by
  apply holds_decode v cl_14114
  have he : decodeClause cl_14114 = containClause5 11 19 := by decide
  rw [he]
  exact input_contain 11 19 (by decide) v h
def cl_14116 : CNF.NClause := [(11,true),(21,true),(486,false)]
theorem inp_14116 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14116 := by
  apply holds_decode v cl_14116
  have he : decodeClause cl_14116 = containClause5 11 21 := by decide
  rw [he]
  exact input_contain 11 21 (by decide) v h
def cl_14118 : CNF.NClause := [(11,true),(23,true),(488,false)]
theorem inp_14118 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14118 := by
  apply holds_decode v cl_14118
  have he : decodeClause cl_14118 = containClause5 11 23 := by decide
  rw [he]
  exact input_contain 11 23 (by decide) v h
def cl_14119 : CNF.NClause := [(11,true),(24,true),(489,false)]
theorem inp_14119 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14119 := by
  apply holds_decode v cl_14119
  have he : decodeClause cl_14119 = containClause5 11 24 := by decide
  rw [he]
  exact input_contain 11 24 (by decide) v h
def cl_14122 : CNF.NClause := [(11,true),(27,true),(492,false)]
theorem inp_14122 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14122 := by
  apply holds_decode v cl_14122
  have he : decodeClause cl_14122 = containClause5 11 27 := by decide
  rw [he]
  exact input_contain 11 27 (by decide) v h
def cl_14123 : CNF.NClause := [(11,true),(28,true),(493,false)]
theorem inp_14123 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14123 := by
  apply holds_decode v cl_14123
  have he : decodeClause cl_14123 = containClause5 11 28 := by decide
  rw [he]
  exact input_contain 11 28 (by decide) v h
def cl_14125 : CNF.NClause := [(11,true),(30,true),(495,false)]
theorem inp_14125 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14125 := by
  apply holds_decode v cl_14125
  have he : decodeClause cl_14125 = containClause5 11 30 := by decide
  rw [he]
  exact input_contain 11 30 (by decide) v h
def cl_14278 : CNF.NClause := [(17,true),(2,true),(653,false)]
theorem inp_14278 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14278 := by
  apply holds_decode v cl_14278
  have he : decodeClause cl_14278 = containClause5 17 2 := by decide
  rw [he]
  exact input_contain 17 2 (by decide) v h
def cl_14282 : CNF.NClause := [(17,true),(6,true),(657,false)]
theorem inp_14282 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14282 := by
  apply holds_decode v cl_14282
  have he : decodeClause cl_14282 = containClause5 17 6 := by decide
  rw [he]
  exact input_contain 17 6 (by decide) v h
def cl_14286 : CNF.NClause := [(17,true),(10,true),(661,false)]
theorem inp_14286 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14286 := by
  apply holds_decode v cl_14286
  have he : decodeClause cl_14286 = containClause5 17 10 := by decide
  rw [he]
  exact input_contain 17 10 (by decide) v h
end Percolation.Replay
