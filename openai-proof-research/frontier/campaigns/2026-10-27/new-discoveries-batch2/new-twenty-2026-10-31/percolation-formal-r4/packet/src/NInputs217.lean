import NInputs216
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14255 : CNF.NClause := [(16,true),(9,true),(629,false)]
theorem inp_14255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14255 = (containClause5 16 9) := by decide
  rw [he]
  exact input_contain 16 9 (by decide) v hb
def cl_14256 : CNF.NClause := [(16,true),(10,true),(630,false)]
theorem inp_14256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14256 = (containClause5 16 10) := by decide
  rw [he]
  exact input_contain 16 10 (by decide) v hb
def cl_14257 : CNF.NClause := [(16,true),(11,true),(631,false)]
theorem inp_14257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14257 = (containClause5 16 11) := by decide
  rw [he]
  exact input_contain 16 11 (by decide) v hb
def cl_14258 : CNF.NClause := [(16,true),(12,true),(632,false)]
theorem inp_14258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14258 = (containClause5 16 12) := by decide
  rw [he]
  exact input_contain 16 12 (by decide) v hb
def cl_14259 : CNF.NClause := [(16,true),(13,true),(633,false)]
theorem inp_14259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14259 = (containClause5 16 13) := by decide
  rw [he]
  exact input_contain 16 13 (by decide) v hb
def cl_14260 : CNF.NClause := [(16,true),(14,true),(634,false)]
theorem inp_14260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14260 = (containClause5 16 14) := by decide
  rw [he]
  exact input_contain 16 14 (by decide) v hb
def cl_14261 : CNF.NClause := [(16,true),(15,true),(635,false)]
theorem inp_14261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14261 = (containClause5 16 15) := by decide
  rw [he]
  exact input_contain 16 15 (by decide) v hb
def cl_14262 : CNF.NClause := [(16,true),(17,true),(637,false)]
theorem inp_14262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14262 = (containClause5 16 17) := by decide
  rw [he]
  exact input_contain 16 17 (by decide) v hb
def cl_14263 : CNF.NClause := [(16,true),(18,true),(638,false)]
theorem inp_14263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14263 = (containClause5 16 18) := by decide
  rw [he]
  exact input_contain 16 18 (by decide) v hb
def cl_14264 : CNF.NClause := [(16,true),(19,true),(639,false)]
theorem inp_14264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14264 = (containClause5 16 19) := by decide
  rw [he]
  exact input_contain 16 19 (by decide) v hb
def cl_14265 : CNF.NClause := [(16,true),(20,true),(640,false)]
theorem inp_14265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14265 = (containClause5 16 20) := by decide
  rw [he]
  exact input_contain 16 20 (by decide) v hb
def cl_14266 : CNF.NClause := [(16,true),(21,true),(641,false)]
theorem inp_14266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14266 = (containClause5 16 21) := by decide
  rw [he]
  exact input_contain 16 21 (by decide) v hb
def cl_14267 : CNF.NClause := [(16,true),(22,true),(642,false)]
theorem inp_14267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14267 = (containClause5 16 22) := by decide
  rw [he]
  exact input_contain 16 22 (by decide) v hb
def cl_14268 : CNF.NClause := [(16,true),(23,true),(643,false)]
theorem inp_14268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14268 = (containClause5 16 23) := by decide
  rw [he]
  exact input_contain 16 23 (by decide) v hb
def cl_14269 : CNF.NClause := [(16,true),(24,true),(644,false)]
theorem inp_14269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14269 = (containClause5 16 24) := by decide
  rw [he]
  exact input_contain 16 24 (by decide) v hb
def cl_14270 : CNF.NClause := [(16,true),(25,true),(645,false)]
theorem inp_14270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14270 = (containClause5 16 25) := by decide
  rw [he]
  exact input_contain 16 25 (by decide) v hb
def cl_14271 : CNF.NClause := [(16,true),(26,true),(646,false)]
theorem inp_14271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14271 = (containClause5 16 26) := by decide
  rw [he]
  exact input_contain 16 26 (by decide) v hb
def cl_14272 : CNF.NClause := [(16,true),(27,true),(647,false)]
theorem inp_14272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14272 = (containClause5 16 27) := by decide
  rw [he]
  exact input_contain 16 27 (by decide) v hb
def cl_14273 : CNF.NClause := [(16,true),(28,true),(648,false)]
theorem inp_14273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14273 = (containClause5 16 28) := by decide
  rw [he]
  exact input_contain 16 28 (by decide) v hb
def cl_14274 : CNF.NClause := [(16,true),(29,true),(649,false)]
theorem inp_14274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14274 = (containClause5 16 29) := by decide
  rw [he]
  exact input_contain 16 29 (by decide) v hb
def cl_14275 : CNF.NClause := [(16,true),(30,true),(650,false)]
theorem inp_14275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14275 = (containClause5 16 30) := by decide
  rw [he]
  exact input_contain 16 30 (by decide) v hb
def cl_14276 : CNF.NClause := [(17,true),(0,true),(651,false)]
theorem inp_14276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14276 = (containClause5 17 0) := by decide
  rw [he]
  exact input_contain 17 0 (by decide) v hb
def cl_14277 : CNF.NClause := [(17,true),(1,true),(652,false)]
theorem inp_14277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14277 = (containClause5 17 1) := by decide
  rw [he]
  exact input_contain 17 1 (by decide) v hb
def cl_14278 : CNF.NClause := [(17,true),(2,true),(653,false)]
theorem inp_14278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14278 v hb
def cl_14279 : CNF.NClause := [(17,true),(3,true),(654,false)]
theorem inp_14279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14279 = (containClause5 17 3) := by decide
  rw [he]
  exact input_contain 17 3 (by decide) v hb
def cl_14280 : CNF.NClause := [(17,true),(4,true),(655,false)]
theorem inp_14280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14280 = (containClause5 17 4) := by decide
  rw [he]
  exact input_contain 17 4 (by decide) v hb
def cl_14281 : CNF.NClause := [(17,true),(5,true),(656,false)]
theorem inp_14281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14281 = (containClause5 17 5) := by decide
  rw [he]
  exact input_contain 17 5 (by decide) v hb
def cl_14282 : CNF.NClause := [(17,true),(6,true),(657,false)]
theorem inp_14282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14282 v hb
def cl_14283 : CNF.NClause := [(17,true),(7,true),(658,false)]
theorem inp_14283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14283 = (containClause5 17 7) := by decide
  rw [he]
  exact input_contain 17 7 (by decide) v hb
def cl_14284 : CNF.NClause := [(17,true),(8,true),(659,false)]
theorem inp_14284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14284 = (containClause5 17 8) := by decide
  rw [he]
  exact input_contain 17 8 (by decide) v hb
def cl_14285 : CNF.NClause := [(17,true),(9,true),(660,false)]
theorem inp_14285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14285 = (containClause5 17 9) := by decide
  rw [he]
  exact input_contain 17 9 (by decide) v hb
def cl_14286 : CNF.NClause := [(17,true),(10,true),(661,false)]
theorem inp_14286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14286 v hb
def cl_14287 : CNF.NClause := [(17,true),(11,true),(662,false)]
theorem inp_14287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14287 = (containClause5 17 11) := by decide
  rw [he]
  exact input_contain 17 11 (by decide) v hb
def cl_14288 : CNF.NClause := [(17,true),(12,true),(663,false)]
theorem inp_14288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14288 = (containClause5 17 12) := by decide
  rw [he]
  exact input_contain 17 12 (by decide) v hb
def cl_14289 : CNF.NClause := [(17,true),(13,true),(664,false)]
theorem inp_14289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14289 = (containClause5 17 13) := by decide
  rw [he]
  exact input_contain 17 13 (by decide) v hb
def cl_14290 : CNF.NClause := [(17,true),(14,true),(665,false)]
theorem inp_14290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14290 = (containClause5 17 14) := by decide
  rw [he]
  exact input_contain 17 14 (by decide) v hb
def cl_14291 : CNF.NClause := [(17,true),(15,true),(666,false)]
theorem inp_14291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14291 = (containClause5 17 15) := by decide
  rw [he]
  exact input_contain 17 15 (by decide) v hb
def cl_14292 : CNF.NClause := [(17,true),(16,true),(667,false)]
theorem inp_14292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14292 = (containClause5 17 16) := by decide
  rw [he]
  exact input_contain 17 16 (by decide) v hb
def cl_14293 : CNF.NClause := [(17,true),(18,true),(669,false)]
theorem inp_14293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14293 = (containClause5 17 18) := by decide
  rw [he]
  exact input_contain 17 18 (by decide) v hb
def cl_14294 : CNF.NClause := [(17,true),(19,true),(670,false)]
theorem inp_14294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14294 v hb
def cl_14295 : CNF.NClause := [(17,true),(20,true),(671,false)]
theorem inp_14295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14295 v hb
def cl_14296 : CNF.NClause := [(17,true),(21,true),(672,false)]
theorem inp_14296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14296 v hb
def cl_14297 : CNF.NClause := [(17,true),(22,true),(673,false)]
theorem inp_14297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14297 v hb
def cl_14298 : CNF.NClause := [(17,true),(23,true),(674,false)]
theorem inp_14298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14298 v hb
def cl_14299 : CNF.NClause := [(17,true),(24,true),(675,false)]
theorem inp_14299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14299 = (containClause5 17 24) := by decide
  rw [he]
  exact input_contain 17 24 (by decide) v hb
def cl_14300 : CNF.NClause := [(17,true),(25,true),(676,false)]
theorem inp_14300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14300 = (containClause5 17 25) := by decide
  rw [he]
  exact input_contain 17 25 (by decide) v hb
def cl_14301 : CNF.NClause := [(17,true),(26,true),(677,false)]
theorem inp_14301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14301 = (containClause5 17 26) := by decide
  rw [he]
  exact input_contain 17 26 (by decide) v hb
def cl_14302 : CNF.NClause := [(17,true),(27,true),(678,false)]
theorem inp_14302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14302 = (containClause5 17 27) := by decide
  rw [he]
  exact input_contain 17 27 (by decide) v hb
def cl_14303 : CNF.NClause := [(17,true),(28,true),(679,false)]
theorem inp_14303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14303 = (containClause5 17 28) := by decide
  rw [he]
  exact input_contain 17 28 (by decide) v hb
def cl_14304 : CNF.NClause := [(17,true),(29,true),(680,false)]
theorem inp_14304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14304 v hb
end Percolation.NReplay
