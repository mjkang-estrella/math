import NInputs213
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14105 : CNF.NClause := [(11,true),(9,true),(474,false)]
theorem inp_14105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14105 v hb
def cl_14106 : CNF.NClause := [(11,true),(10,true),(475,false)]
theorem inp_14106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14106 v hb
def cl_14107 : CNF.NClause := [(11,true),(12,true),(477,false)]
theorem inp_14107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14107 v hb
def cl_14108 : CNF.NClause := [(11,true),(13,true),(478,false)]
theorem inp_14108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14108 v hb
def cl_14109 : CNF.NClause := [(11,true),(14,true),(479,false)]
theorem inp_14109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14109 v hb
def cl_14110 : CNF.NClause := [(11,true),(15,true),(480,false)]
theorem inp_14110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14110 v hb
def cl_14111 : CNF.NClause := [(11,true),(16,true),(481,false)]
theorem inp_14111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14111 v hb
def cl_14112 : CNF.NClause := [(11,true),(17,true),(482,false)]
theorem inp_14112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14112 = (containClause5 11 17) := by decide
  rw [he]
  exact input_contain 11 17 (by decide) v hb
def cl_14113 : CNF.NClause := [(11,true),(18,true),(483,false)]
theorem inp_14113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14113 v hb
def cl_14114 : CNF.NClause := [(11,true),(19,true),(484,false)]
theorem inp_14114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14114 v hb
def cl_14115 : CNF.NClause := [(11,true),(20,true),(485,false)]
theorem inp_14115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14115 = (containClause5 11 20) := by decide
  rw [he]
  exact input_contain 11 20 (by decide) v hb
def cl_14116 : CNF.NClause := [(11,true),(21,true),(486,false)]
theorem inp_14116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14116 v hb
def cl_14117 : CNF.NClause := [(11,true),(22,true),(487,false)]
theorem inp_14117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14117 = (containClause5 11 22) := by decide
  rw [he]
  exact input_contain 11 22 (by decide) v hb
def cl_14118 : CNF.NClause := [(11,true),(23,true),(488,false)]
theorem inp_14118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14118 v hb
def cl_14119 : CNF.NClause := [(11,true),(24,true),(489,false)]
theorem inp_14119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14119 v hb
def cl_14120 : CNF.NClause := [(11,true),(25,true),(490,false)]
theorem inp_14120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14120 = (containClause5 11 25) := by decide
  rw [he]
  exact input_contain 11 25 (by decide) v hb
def cl_14121 : CNF.NClause := [(11,true),(26,true),(491,false)]
theorem inp_14121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14121 = (containClause5 11 26) := by decide
  rw [he]
  exact input_contain 11 26 (by decide) v hb
def cl_14122 : CNF.NClause := [(11,true),(27,true),(492,false)]
theorem inp_14122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14122 v hb
def cl_14123 : CNF.NClause := [(11,true),(28,true),(493,false)]
theorem inp_14123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14123 v hb
def cl_14124 : CNF.NClause := [(11,true),(29,true),(494,false)]
theorem inp_14124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14124 = (containClause5 11 29) := by decide
  rw [he]
  exact input_contain 11 29 (by decide) v hb
def cl_14125 : CNF.NClause := [(11,true),(30,true),(495,false)]
theorem inp_14125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14125 v hb
def cl_14126 : CNF.NClause := [(12,true),(0,true),(496,false)]
theorem inp_14126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14126 = (containClause5 12 0) := by decide
  rw [he]
  exact input_contain 12 0 (by decide) v hb
def cl_14127 : CNF.NClause := [(12,true),(1,true),(497,false)]
theorem inp_14127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14127 = (containClause5 12 1) := by decide
  rw [he]
  exact input_contain 12 1 (by decide) v hb
def cl_14128 : CNF.NClause := [(12,true),(2,true),(498,false)]
theorem inp_14128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14128 = (containClause5 12 2) := by decide
  rw [he]
  exact input_contain 12 2 (by decide) v hb
def cl_14129 : CNF.NClause := [(12,true),(3,true),(499,false)]
theorem inp_14129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14129 = (containClause5 12 3) := by decide
  rw [he]
  exact input_contain 12 3 (by decide) v hb
def cl_14130 : CNF.NClause := [(12,true),(4,true),(500,false)]
theorem inp_14130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14130 = (containClause5 12 4) := by decide
  rw [he]
  exact input_contain 12 4 (by decide) v hb
def cl_14131 : CNF.NClause := [(12,true),(5,true),(501,false)]
theorem inp_14131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14131 = (containClause5 12 5) := by decide
  rw [he]
  exact input_contain 12 5 (by decide) v hb
def cl_14132 : CNF.NClause := [(12,true),(6,true),(502,false)]
theorem inp_14132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14132 = (containClause5 12 6) := by decide
  rw [he]
  exact input_contain 12 6 (by decide) v hb
def cl_14133 : CNF.NClause := [(12,true),(7,true),(503,false)]
theorem inp_14133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14133 = (containClause5 12 7) := by decide
  rw [he]
  exact input_contain 12 7 (by decide) v hb
def cl_14134 : CNF.NClause := [(12,true),(8,true),(504,false)]
theorem inp_14134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14134 = (containClause5 12 8) := by decide
  rw [he]
  exact input_contain 12 8 (by decide) v hb
def cl_14135 : CNF.NClause := [(12,true),(9,true),(505,false)]
theorem inp_14135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14135 = (containClause5 12 9) := by decide
  rw [he]
  exact input_contain 12 9 (by decide) v hb
def cl_14136 : CNF.NClause := [(12,true),(10,true),(506,false)]
theorem inp_14136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14136 = (containClause5 12 10) := by decide
  rw [he]
  exact input_contain 12 10 (by decide) v hb
def cl_14137 : CNF.NClause := [(12,true),(11,true),(507,false)]
theorem inp_14137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14137 = (containClause5 12 11) := by decide
  rw [he]
  exact input_contain 12 11 (by decide) v hb
def cl_14138 : CNF.NClause := [(12,true),(13,true),(509,false)]
theorem inp_14138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14138 = (containClause5 12 13) := by decide
  rw [he]
  exact input_contain 12 13 (by decide) v hb
def cl_14139 : CNF.NClause := [(12,true),(14,true),(510,false)]
theorem inp_14139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14139 = (containClause5 12 14) := by decide
  rw [he]
  exact input_contain 12 14 (by decide) v hb
def cl_14140 : CNF.NClause := [(12,true),(15,true),(511,false)]
theorem inp_14140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14140 = (containClause5 12 15) := by decide
  rw [he]
  exact input_contain 12 15 (by decide) v hb
def cl_14141 : CNF.NClause := [(12,true),(16,true),(512,false)]
theorem inp_14141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14141 = (containClause5 12 16) := by decide
  rw [he]
  exact input_contain 12 16 (by decide) v hb
def cl_14142 : CNF.NClause := [(12,true),(17,true),(513,false)]
theorem inp_14142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14142 = (containClause5 12 17) := by decide
  rw [he]
  exact input_contain 12 17 (by decide) v hb
def cl_14143 : CNF.NClause := [(12,true),(18,true),(514,false)]
theorem inp_14143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14143 = (containClause5 12 18) := by decide
  rw [he]
  exact input_contain 12 18 (by decide) v hb
def cl_14144 : CNF.NClause := [(12,true),(19,true),(515,false)]
theorem inp_14144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14144 = (containClause5 12 19) := by decide
  rw [he]
  exact input_contain 12 19 (by decide) v hb
def cl_14145 : CNF.NClause := [(12,true),(20,true),(516,false)]
theorem inp_14145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14145 = (containClause5 12 20) := by decide
  rw [he]
  exact input_contain 12 20 (by decide) v hb
def cl_14146 : CNF.NClause := [(12,true),(21,true),(517,false)]
theorem inp_14146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14146 = (containClause5 12 21) := by decide
  rw [he]
  exact input_contain 12 21 (by decide) v hb
def cl_14147 : CNF.NClause := [(12,true),(22,true),(518,false)]
theorem inp_14147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14147 = (containClause5 12 22) := by decide
  rw [he]
  exact input_contain 12 22 (by decide) v hb
def cl_14148 : CNF.NClause := [(12,true),(23,true),(519,false)]
theorem inp_14148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14148 = (containClause5 12 23) := by decide
  rw [he]
  exact input_contain 12 23 (by decide) v hb
def cl_14149 : CNF.NClause := [(12,true),(24,true),(520,false)]
theorem inp_14149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14149 = (containClause5 12 24) := by decide
  rw [he]
  exact input_contain 12 24 (by decide) v hb
def cl_14150 : CNF.NClause := [(12,true),(25,true),(521,false)]
theorem inp_14150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14150 = (containClause5 12 25) := by decide
  rw [he]
  exact input_contain 12 25 (by decide) v hb
def cl_14151 : CNF.NClause := [(12,true),(26,true),(522,false)]
theorem inp_14151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14151 = (containClause5 12 26) := by decide
  rw [he]
  exact input_contain 12 26 (by decide) v hb
def cl_14152 : CNF.NClause := [(12,true),(27,true),(523,false)]
theorem inp_14152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14152 = (containClause5 12 27) := by decide
  rw [he]
  exact input_contain 12 27 (by decide) v hb
def cl_14153 : CNF.NClause := [(12,true),(28,true),(524,false)]
theorem inp_14153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14153 = (containClause5 12 28) := by decide
  rw [he]
  exact input_contain 12 28 (by decide) v hb
def cl_14154 : CNF.NClause := [(12,true),(29,true),(525,false)]
theorem inp_14154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14154 = (containClause5 12 29) := by decide
  rw [he]
  exact input_contain 12 29 (by decide) v hb
end Percolation.NReplay
