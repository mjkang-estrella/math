import NInputs215
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14205 : CNF.NClause := [(14,true),(20,true),(578,false)]
theorem inp_14205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14205 = (containClause5 14 20) := by decide
  rw [he]
  exact input_contain 14 20 (by decide) v hb
def cl_14206 : CNF.NClause := [(14,true),(21,true),(579,false)]
theorem inp_14206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14206 = (containClause5 14 21) := by decide
  rw [he]
  exact input_contain 14 21 (by decide) v hb
def cl_14207 : CNF.NClause := [(14,true),(22,true),(580,false)]
theorem inp_14207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14207 = (containClause5 14 22) := by decide
  rw [he]
  exact input_contain 14 22 (by decide) v hb
def cl_14208 : CNF.NClause := [(14,true),(23,true),(581,false)]
theorem inp_14208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14208 = (containClause5 14 23) := by decide
  rw [he]
  exact input_contain 14 23 (by decide) v hb
def cl_14209 : CNF.NClause := [(14,true),(24,true),(582,false)]
theorem inp_14209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14209 = (containClause5 14 24) := by decide
  rw [he]
  exact input_contain 14 24 (by decide) v hb
def cl_14210 : CNF.NClause := [(14,true),(25,true),(583,false)]
theorem inp_14210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14210 = (containClause5 14 25) := by decide
  rw [he]
  exact input_contain 14 25 (by decide) v hb
def cl_14211 : CNF.NClause := [(14,true),(26,true),(584,false)]
theorem inp_14211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14211 = (containClause5 14 26) := by decide
  rw [he]
  exact input_contain 14 26 (by decide) v hb
def cl_14212 : CNF.NClause := [(14,true),(27,true),(585,false)]
theorem inp_14212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14212 = (containClause5 14 27) := by decide
  rw [he]
  exact input_contain 14 27 (by decide) v hb
def cl_14213 : CNF.NClause := [(14,true),(28,true),(586,false)]
theorem inp_14213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14213 = (containClause5 14 28) := by decide
  rw [he]
  exact input_contain 14 28 (by decide) v hb
def cl_14214 : CNF.NClause := [(14,true),(29,true),(587,false)]
theorem inp_14214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14214 = (containClause5 14 29) := by decide
  rw [he]
  exact input_contain 14 29 (by decide) v hb
def cl_14215 : CNF.NClause := [(14,true),(30,true),(588,false)]
theorem inp_14215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14215 = (containClause5 14 30) := by decide
  rw [he]
  exact input_contain 14 30 (by decide) v hb
def cl_14216 : CNF.NClause := [(15,true),(0,true),(589,false)]
theorem inp_14216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14216 = (containClause5 15 0) := by decide
  rw [he]
  exact input_contain 15 0 (by decide) v hb
def cl_14217 : CNF.NClause := [(15,true),(1,true),(590,false)]
theorem inp_14217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14217 = (containClause5 15 1) := by decide
  rw [he]
  exact input_contain 15 1 (by decide) v hb
def cl_14218 : CNF.NClause := [(15,true),(2,true),(591,false)]
theorem inp_14218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14218 = (containClause5 15 2) := by decide
  rw [he]
  exact input_contain 15 2 (by decide) v hb
def cl_14219 : CNF.NClause := [(15,true),(3,true),(592,false)]
theorem inp_14219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14219 = (containClause5 15 3) := by decide
  rw [he]
  exact input_contain 15 3 (by decide) v hb
def cl_14220 : CNF.NClause := [(15,true),(4,true),(593,false)]
theorem inp_14220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14220 = (containClause5 15 4) := by decide
  rw [he]
  exact input_contain 15 4 (by decide) v hb
def cl_14221 : CNF.NClause := [(15,true),(5,true),(594,false)]
theorem inp_14221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14221 = (containClause5 15 5) := by decide
  rw [he]
  exact input_contain 15 5 (by decide) v hb
def cl_14222 : CNF.NClause := [(15,true),(6,true),(595,false)]
theorem inp_14222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14222 = (containClause5 15 6) := by decide
  rw [he]
  exact input_contain 15 6 (by decide) v hb
def cl_14223 : CNF.NClause := [(15,true),(7,true),(596,false)]
theorem inp_14223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14223 = (containClause5 15 7) := by decide
  rw [he]
  exact input_contain 15 7 (by decide) v hb
def cl_14224 : CNF.NClause := [(15,true),(8,true),(597,false)]
theorem inp_14224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14224 = (containClause5 15 8) := by decide
  rw [he]
  exact input_contain 15 8 (by decide) v hb
def cl_14225 : CNF.NClause := [(15,true),(9,true),(598,false)]
theorem inp_14225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14225 = (containClause5 15 9) := by decide
  rw [he]
  exact input_contain 15 9 (by decide) v hb
def cl_14226 : CNF.NClause := [(15,true),(10,true),(599,false)]
theorem inp_14226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14226 = (containClause5 15 10) := by decide
  rw [he]
  exact input_contain 15 10 (by decide) v hb
def cl_14227 : CNF.NClause := [(15,true),(11,true),(600,false)]
theorem inp_14227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14227 = (containClause5 15 11) := by decide
  rw [he]
  exact input_contain 15 11 (by decide) v hb
def cl_14228 : CNF.NClause := [(15,true),(12,true),(601,false)]
theorem inp_14228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14228 = (containClause5 15 12) := by decide
  rw [he]
  exact input_contain 15 12 (by decide) v hb
def cl_14229 : CNF.NClause := [(15,true),(13,true),(602,false)]
theorem inp_14229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14229 = (containClause5 15 13) := by decide
  rw [he]
  exact input_contain 15 13 (by decide) v hb
def cl_14230 : CNF.NClause := [(15,true),(14,true),(603,false)]
theorem inp_14230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14230 = (containClause5 15 14) := by decide
  rw [he]
  exact input_contain 15 14 (by decide) v hb
def cl_14231 : CNF.NClause := [(15,true),(16,true),(605,false)]
theorem inp_14231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14231 = (containClause5 15 16) := by decide
  rw [he]
  exact input_contain 15 16 (by decide) v hb
def cl_14232 : CNF.NClause := [(15,true),(17,true),(606,false)]
theorem inp_14232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14232 = (containClause5 15 17) := by decide
  rw [he]
  exact input_contain 15 17 (by decide) v hb
def cl_14233 : CNF.NClause := [(15,true),(18,true),(607,false)]
theorem inp_14233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14233 = (containClause5 15 18) := by decide
  rw [he]
  exact input_contain 15 18 (by decide) v hb
def cl_14234 : CNF.NClause := [(15,true),(19,true),(608,false)]
theorem inp_14234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14234 = (containClause5 15 19) := by decide
  rw [he]
  exact input_contain 15 19 (by decide) v hb
def cl_14235 : CNF.NClause := [(15,true),(20,true),(609,false)]
theorem inp_14235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14235 = (containClause5 15 20) := by decide
  rw [he]
  exact input_contain 15 20 (by decide) v hb
def cl_14236 : CNF.NClause := [(15,true),(21,true),(610,false)]
theorem inp_14236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14236 = (containClause5 15 21) := by decide
  rw [he]
  exact input_contain 15 21 (by decide) v hb
def cl_14237 : CNF.NClause := [(15,true),(22,true),(611,false)]
theorem inp_14237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14237 = (containClause5 15 22) := by decide
  rw [he]
  exact input_contain 15 22 (by decide) v hb
def cl_14238 : CNF.NClause := [(15,true),(23,true),(612,false)]
theorem inp_14238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14238 = (containClause5 15 23) := by decide
  rw [he]
  exact input_contain 15 23 (by decide) v hb
def cl_14239 : CNF.NClause := [(15,true),(24,true),(613,false)]
theorem inp_14239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14239 = (containClause5 15 24) := by decide
  rw [he]
  exact input_contain 15 24 (by decide) v hb
def cl_14240 : CNF.NClause := [(15,true),(25,true),(614,false)]
theorem inp_14240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14240 = (containClause5 15 25) := by decide
  rw [he]
  exact input_contain 15 25 (by decide) v hb
def cl_14241 : CNF.NClause := [(15,true),(26,true),(615,false)]
theorem inp_14241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14241 = (containClause5 15 26) := by decide
  rw [he]
  exact input_contain 15 26 (by decide) v hb
def cl_14242 : CNF.NClause := [(15,true),(27,true),(616,false)]
theorem inp_14242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14242 = (containClause5 15 27) := by decide
  rw [he]
  exact input_contain 15 27 (by decide) v hb
def cl_14243 : CNF.NClause := [(15,true),(28,true),(617,false)]
theorem inp_14243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14243 = (containClause5 15 28) := by decide
  rw [he]
  exact input_contain 15 28 (by decide) v hb
def cl_14244 : CNF.NClause := [(15,true),(29,true),(618,false)]
theorem inp_14244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14244 = (containClause5 15 29) := by decide
  rw [he]
  exact input_contain 15 29 (by decide) v hb
def cl_14245 : CNF.NClause := [(15,true),(30,true),(619,false)]
theorem inp_14245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14245 = (containClause5 15 30) := by decide
  rw [he]
  exact input_contain 15 30 (by decide) v hb
def cl_14246 : CNF.NClause := [(16,true),(0,true),(620,false)]
theorem inp_14246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14246 = (containClause5 16 0) := by decide
  rw [he]
  exact input_contain 16 0 (by decide) v hb
def cl_14247 : CNF.NClause := [(16,true),(1,true),(621,false)]
theorem inp_14247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14247 = (containClause5 16 1) := by decide
  rw [he]
  exact input_contain 16 1 (by decide) v hb
def cl_14248 : CNF.NClause := [(16,true),(2,true),(622,false)]
theorem inp_14248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14248 = (containClause5 16 2) := by decide
  rw [he]
  exact input_contain 16 2 (by decide) v hb
def cl_14249 : CNF.NClause := [(16,true),(3,true),(623,false)]
theorem inp_14249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14249 = (containClause5 16 3) := by decide
  rw [he]
  exact input_contain 16 3 (by decide) v hb
def cl_14250 : CNF.NClause := [(16,true),(4,true),(624,false)]
theorem inp_14250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14250 = (containClause5 16 4) := by decide
  rw [he]
  exact input_contain 16 4 (by decide) v hb
def cl_14251 : CNF.NClause := [(16,true),(5,true),(625,false)]
theorem inp_14251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14251 = (containClause5 16 5) := by decide
  rw [he]
  exact input_contain 16 5 (by decide) v hb
def cl_14252 : CNF.NClause := [(16,true),(6,true),(626,false)]
theorem inp_14252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14252 = (containClause5 16 6) := by decide
  rw [he]
  exact input_contain 16 6 (by decide) v hb
def cl_14253 : CNF.NClause := [(16,true),(7,true),(627,false)]
theorem inp_14253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14253 = (containClause5 16 7) := by decide
  rw [he]
  exact input_contain 16 7 (by decide) v hb
def cl_14254 : CNF.NClause := [(16,true),(8,true),(628,false)]
theorem inp_14254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14254 = (containClause5 16 8) := by decide
  rw [he]
  exact input_contain 16 8 (by decide) v hb
end Percolation.NReplay
