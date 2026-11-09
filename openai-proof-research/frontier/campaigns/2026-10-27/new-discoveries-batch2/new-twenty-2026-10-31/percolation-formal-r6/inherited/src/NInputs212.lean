import NInputs211
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14005 : CNF.NClause := [(7,true),(30,true),(371,false)]
theorem inp_14005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14005 v hb
def cl_14006 : CNF.NClause := [(8,true),(0,true),(372,false)]
theorem inp_14006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14006 v hb
def cl_14007 : CNF.NClause := [(8,true),(1,true),(373,false)]
theorem inp_14007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14007 = (containClause5 8 1) := by decide
  rw [he]
  exact input_contain 8 1 (by decide) v hb
def cl_14008 : CNF.NClause := [(8,true),(2,true),(374,false)]
theorem inp_14008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14008 v hb
def cl_14009 : CNF.NClause := [(8,true),(3,true),(375,false)]
theorem inp_14009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14009 v hb
def cl_14010 : CNF.NClause := [(8,true),(4,true),(376,false)]
theorem inp_14010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14010 v hb
def cl_14011 : CNF.NClause := [(8,true),(5,true),(377,false)]
theorem inp_14011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14011 v hb
def cl_14012 : CNF.NClause := [(8,true),(6,true),(378,false)]
theorem inp_14012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14012 = (containClause5 8 6) := by decide
  rw [he]
  exact input_contain 8 6 (by decide) v hb
def cl_14013 : CNF.NClause := [(8,true),(7,true),(379,false)]
theorem inp_14013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14013 = (containClause5 8 7) := by decide
  rw [he]
  exact input_contain 8 7 (by decide) v hb
def cl_14014 : CNF.NClause := [(8,true),(9,true),(381,false)]
theorem inp_14014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14014 v hb
def cl_14015 : CNF.NClause := [(8,true),(10,true),(382,false)]
theorem inp_14015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14015 = (containClause5 8 10) := by decide
  rw [he]
  exact input_contain 8 10 (by decide) v hb
def cl_14016 : CNF.NClause := [(8,true),(11,true),(383,false)]
theorem inp_14016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14016 = (containClause5 8 11) := by decide
  rw [he]
  exact input_contain 8 11 (by decide) v hb
def cl_14017 : CNF.NClause := [(8,true),(12,true),(384,false)]
theorem inp_14017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14017 = (containClause5 8 12) := by decide
  rw [he]
  exact input_contain 8 12 (by decide) v hb
def cl_14018 : CNF.NClause := [(8,true),(13,true),(385,false)]
theorem inp_14018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14018 v hb
def cl_14019 : CNF.NClause := [(8,true),(14,true),(386,false)]
theorem inp_14019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14019 = (containClause5 8 14) := by decide
  rw [he]
  exact input_contain 8 14 (by decide) v hb
def cl_14020 : CNF.NClause := [(8,true),(15,true),(387,false)]
theorem inp_14020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14020 = (containClause5 8 15) := by decide
  rw [he]
  exact input_contain 8 15 (by decide) v hb
def cl_14021 : CNF.NClause := [(8,true),(16,true),(388,false)]
theorem inp_14021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14021 v hb
def cl_14022 : CNF.NClause := [(8,true),(17,true),(389,false)]
theorem inp_14022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14022 v hb
def cl_14023 : CNF.NClause := [(8,true),(18,true),(390,false)]
theorem inp_14023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14023 = (containClause5 8 18) := by decide
  rw [he]
  exact input_contain 8 18 (by decide) v hb
def cl_14024 : CNF.NClause := [(8,true),(19,true),(391,false)]
theorem inp_14024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14024 = (containClause5 8 19) := by decide
  rw [he]
  exact input_contain 8 19 (by decide) v hb
def cl_14025 : CNF.NClause := [(8,true),(20,true),(392,false)]
theorem inp_14025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14025 v hb
def cl_14026 : CNF.NClause := [(8,true),(21,true),(393,false)]
theorem inp_14026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14026 v hb
def cl_14027 : CNF.NClause := [(8,true),(22,true),(394,false)]
theorem inp_14027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14027 = (containClause5 8 22) := by decide
  rw [he]
  exact input_contain 8 22 (by decide) v hb
def cl_14028 : CNF.NClause := [(8,true),(23,true),(395,false)]
theorem inp_14028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14028 v hb
def cl_14029 : CNF.NClause := [(8,true),(24,true),(396,false)]
theorem inp_14029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14029 v hb
def cl_14030 : CNF.NClause := [(8,true),(25,true),(397,false)]
theorem inp_14030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14030 v hb
def cl_14031 : CNF.NClause := [(8,true),(26,true),(398,false)]
theorem inp_14031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14031 = (containClause5 8 26) := by decide
  rw [he]
  exact input_contain 8 26 (by decide) v hb
def cl_14032 : CNF.NClause := [(8,true),(27,true),(399,false)]
theorem inp_14032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14032 = (containClause5 8 27) := by decide
  rw [he]
  exact input_contain 8 27 (by decide) v hb
def cl_14033 : CNF.NClause := [(8,true),(28,true),(400,false)]
theorem inp_14033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14033 v hb
def cl_14034 : CNF.NClause := [(8,true),(29,true),(401,false)]
theorem inp_14034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14034 v hb
def cl_14035 : CNF.NClause := [(8,true),(30,true),(402,false)]
theorem inp_14035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14035 = (containClause5 8 30) := by decide
  rw [he]
  exact input_contain 8 30 (by decide) v hb
def cl_14036 : CNF.NClause := [(9,true),(0,true),(403,false)]
theorem inp_14036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14036 = (containClause5 9 0) := by decide
  rw [he]
  exact input_contain 9 0 (by decide) v hb
def cl_14037 : CNF.NClause := [(9,true),(1,true),(404,false)]
theorem inp_14037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14037 = (containClause5 9 1) := by decide
  rw [he]
  exact input_contain 9 1 (by decide) v hb
def cl_14038 : CNF.NClause := [(9,true),(2,true),(405,false)]
theorem inp_14038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14038 = (containClause5 9 2) := by decide
  rw [he]
  exact input_contain 9 2 (by decide) v hb
def cl_14039 : CNF.NClause := [(9,true),(3,true),(406,false)]
theorem inp_14039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14039 v hb
def cl_14040 : CNF.NClause := [(9,true),(4,true),(407,false)]
theorem inp_14040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14040 v hb
def cl_14041 : CNF.NClause := [(9,true),(5,true),(408,false)]
theorem inp_14041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14041 = (containClause5 9 5) := by decide
  rw [he]
  exact input_contain 9 5 (by decide) v hb
def cl_14042 : CNF.NClause := [(9,true),(6,true),(409,false)]
theorem inp_14042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14042 = (containClause5 9 6) := by decide
  rw [he]
  exact input_contain 9 6 (by decide) v hb
def cl_14043 : CNF.NClause := [(9,true),(7,true),(410,false)]
theorem inp_14043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14043 = (containClause5 9 7) := by decide
  rw [he]
  exact input_contain 9 7 (by decide) v hb
def cl_14044 : CNF.NClause := [(9,true),(8,true),(411,false)]
theorem inp_14044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14044 v hb
def cl_14045 : CNF.NClause := [(9,true),(10,true),(413,false)]
theorem inp_14045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14045 = (containClause5 9 10) := by decide
  rw [he]
  exact input_contain 9 10 (by decide) v hb
def cl_14046 : CNF.NClause := [(9,true),(11,true),(414,false)]
theorem inp_14046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14046 = (containClause5 9 11) := by decide
  rw [he]
  exact input_contain 9 11 (by decide) v hb
def cl_14047 : CNF.NClause := [(9,true),(12,true),(415,false)]
theorem inp_14047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14047 v hb
def cl_14048 : CNF.NClause := [(9,true),(13,true),(416,false)]
theorem inp_14048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14048 = (containClause5 9 13) := by decide
  rw [he]
  exact input_contain 9 13 (by decide) v hb
def cl_14049 : CNF.NClause := [(9,true),(14,true),(417,false)]
theorem inp_14049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14049 v hb
def cl_14050 : CNF.NClause := [(9,true),(15,true),(418,false)]
theorem inp_14050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14050 v hb
def cl_14051 : CNF.NClause := [(9,true),(16,true),(419,false)]
theorem inp_14051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14051 v hb
def cl_14052 : CNF.NClause := [(9,true),(17,true),(420,false)]
theorem inp_14052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14052 v hb
def cl_14053 : CNF.NClause := [(9,true),(18,true),(421,false)]
theorem inp_14053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14053 = (containClause5 9 18) := by decide
  rw [he]
  exact input_contain 9 18 (by decide) v hb
def cl_14054 : CNF.NClause := [(9,true),(19,true),(422,false)]
theorem inp_14054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14054 = (containClause5 9 19) := by decide
  rw [he]
  exact input_contain 9 19 (by decide) v hb
end Percolation.NReplay
