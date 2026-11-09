import NInputs214
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14155 : CNF.NClause := [(12,true),(30,true),(526,false)]
theorem inp_14155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14155 = (containClause5 12 30) := by decide
  rw [he]
  exact input_contain 12 30 (by decide) v hb
def cl_14156 : CNF.NClause := [(13,true),(0,true),(527,false)]
theorem inp_14156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14156 = (containClause5 13 0) := by decide
  rw [he]
  exact input_contain 13 0 (by decide) v hb
def cl_14157 : CNF.NClause := [(13,true),(1,true),(528,false)]
theorem inp_14157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14157 = (containClause5 13 1) := by decide
  rw [he]
  exact input_contain 13 1 (by decide) v hb
def cl_14158 : CNF.NClause := [(13,true),(2,true),(529,false)]
theorem inp_14158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14158 = (containClause5 13 2) := by decide
  rw [he]
  exact input_contain 13 2 (by decide) v hb
def cl_14159 : CNF.NClause := [(13,true),(3,true),(530,false)]
theorem inp_14159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14159 = (containClause5 13 3) := by decide
  rw [he]
  exact input_contain 13 3 (by decide) v hb
def cl_14160 : CNF.NClause := [(13,true),(4,true),(531,false)]
theorem inp_14160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14160 = (containClause5 13 4) := by decide
  rw [he]
  exact input_contain 13 4 (by decide) v hb
def cl_14161 : CNF.NClause := [(13,true),(5,true),(532,false)]
theorem inp_14161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14161 = (containClause5 13 5) := by decide
  rw [he]
  exact input_contain 13 5 (by decide) v hb
def cl_14162 : CNF.NClause := [(13,true),(6,true),(533,false)]
theorem inp_14162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14162 = (containClause5 13 6) := by decide
  rw [he]
  exact input_contain 13 6 (by decide) v hb
def cl_14163 : CNF.NClause := [(13,true),(7,true),(534,false)]
theorem inp_14163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14163 = (containClause5 13 7) := by decide
  rw [he]
  exact input_contain 13 7 (by decide) v hb
def cl_14164 : CNF.NClause := [(13,true),(8,true),(535,false)]
theorem inp_14164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14164 = (containClause5 13 8) := by decide
  rw [he]
  exact input_contain 13 8 (by decide) v hb
def cl_14165 : CNF.NClause := [(13,true),(9,true),(536,false)]
theorem inp_14165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14165 = (containClause5 13 9) := by decide
  rw [he]
  exact input_contain 13 9 (by decide) v hb
def cl_14166 : CNF.NClause := [(13,true),(10,true),(537,false)]
theorem inp_14166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14166 = (containClause5 13 10) := by decide
  rw [he]
  exact input_contain 13 10 (by decide) v hb
def cl_14167 : CNF.NClause := [(13,true),(11,true),(538,false)]
theorem inp_14167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14167 = (containClause5 13 11) := by decide
  rw [he]
  exact input_contain 13 11 (by decide) v hb
def cl_14168 : CNF.NClause := [(13,true),(12,true),(539,false)]
theorem inp_14168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14168 = (containClause5 13 12) := by decide
  rw [he]
  exact input_contain 13 12 (by decide) v hb
def cl_14169 : CNF.NClause := [(13,true),(14,true),(541,false)]
theorem inp_14169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14169 = (containClause5 13 14) := by decide
  rw [he]
  exact input_contain 13 14 (by decide) v hb
def cl_14170 : CNF.NClause := [(13,true),(15,true),(542,false)]
theorem inp_14170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14170 = (containClause5 13 15) := by decide
  rw [he]
  exact input_contain 13 15 (by decide) v hb
def cl_14171 : CNF.NClause := [(13,true),(16,true),(543,false)]
theorem inp_14171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14171 = (containClause5 13 16) := by decide
  rw [he]
  exact input_contain 13 16 (by decide) v hb
def cl_14172 : CNF.NClause := [(13,true),(17,true),(544,false)]
theorem inp_14172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14172 = (containClause5 13 17) := by decide
  rw [he]
  exact input_contain 13 17 (by decide) v hb
def cl_14173 : CNF.NClause := [(13,true),(18,true),(545,false)]
theorem inp_14173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14173 = (containClause5 13 18) := by decide
  rw [he]
  exact input_contain 13 18 (by decide) v hb
def cl_14174 : CNF.NClause := [(13,true),(19,true),(546,false)]
theorem inp_14174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14174 = (containClause5 13 19) := by decide
  rw [he]
  exact input_contain 13 19 (by decide) v hb
def cl_14175 : CNF.NClause := [(13,true),(20,true),(547,false)]
theorem inp_14175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14175 = (containClause5 13 20) := by decide
  rw [he]
  exact input_contain 13 20 (by decide) v hb
def cl_14176 : CNF.NClause := [(13,true),(21,true),(548,false)]
theorem inp_14176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14176 = (containClause5 13 21) := by decide
  rw [he]
  exact input_contain 13 21 (by decide) v hb
def cl_14177 : CNF.NClause := [(13,true),(22,true),(549,false)]
theorem inp_14177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14177 = (containClause5 13 22) := by decide
  rw [he]
  exact input_contain 13 22 (by decide) v hb
def cl_14178 : CNF.NClause := [(13,true),(23,true),(550,false)]
theorem inp_14178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14178 = (containClause5 13 23) := by decide
  rw [he]
  exact input_contain 13 23 (by decide) v hb
def cl_14179 : CNF.NClause := [(13,true),(24,true),(551,false)]
theorem inp_14179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14179 = (containClause5 13 24) := by decide
  rw [he]
  exact input_contain 13 24 (by decide) v hb
def cl_14180 : CNF.NClause := [(13,true),(25,true),(552,false)]
theorem inp_14180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14180 = (containClause5 13 25) := by decide
  rw [he]
  exact input_contain 13 25 (by decide) v hb
def cl_14181 : CNF.NClause := [(13,true),(26,true),(553,false)]
theorem inp_14181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14181 = (containClause5 13 26) := by decide
  rw [he]
  exact input_contain 13 26 (by decide) v hb
def cl_14182 : CNF.NClause := [(13,true),(27,true),(554,false)]
theorem inp_14182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14182 = (containClause5 13 27) := by decide
  rw [he]
  exact input_contain 13 27 (by decide) v hb
def cl_14183 : CNF.NClause := [(13,true),(28,true),(555,false)]
theorem inp_14183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14183 = (containClause5 13 28) := by decide
  rw [he]
  exact input_contain 13 28 (by decide) v hb
def cl_14184 : CNF.NClause := [(13,true),(29,true),(556,false)]
theorem inp_14184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14184 = (containClause5 13 29) := by decide
  rw [he]
  exact input_contain 13 29 (by decide) v hb
def cl_14185 : CNF.NClause := [(13,true),(30,true),(557,false)]
theorem inp_14185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14185 = (containClause5 13 30) := by decide
  rw [he]
  exact input_contain 13 30 (by decide) v hb
def cl_14186 : CNF.NClause := [(14,true),(0,true),(558,false)]
theorem inp_14186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14186 = (containClause5 14 0) := by decide
  rw [he]
  exact input_contain 14 0 (by decide) v hb
def cl_14187 : CNF.NClause := [(14,true),(1,true),(559,false)]
theorem inp_14187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14187 = (containClause5 14 1) := by decide
  rw [he]
  exact input_contain 14 1 (by decide) v hb
def cl_14188 : CNF.NClause := [(14,true),(2,true),(560,false)]
theorem inp_14188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14188 = (containClause5 14 2) := by decide
  rw [he]
  exact input_contain 14 2 (by decide) v hb
def cl_14189 : CNF.NClause := [(14,true),(3,true),(561,false)]
theorem inp_14189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14189 = (containClause5 14 3) := by decide
  rw [he]
  exact input_contain 14 3 (by decide) v hb
def cl_14190 : CNF.NClause := [(14,true),(4,true),(562,false)]
theorem inp_14190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14190 = (containClause5 14 4) := by decide
  rw [he]
  exact input_contain 14 4 (by decide) v hb
def cl_14191 : CNF.NClause := [(14,true),(5,true),(563,false)]
theorem inp_14191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14191 = (containClause5 14 5) := by decide
  rw [he]
  exact input_contain 14 5 (by decide) v hb
def cl_14192 : CNF.NClause := [(14,true),(6,true),(564,false)]
theorem inp_14192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14192 = (containClause5 14 6) := by decide
  rw [he]
  exact input_contain 14 6 (by decide) v hb
def cl_14193 : CNF.NClause := [(14,true),(7,true),(565,false)]
theorem inp_14193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14193 = (containClause5 14 7) := by decide
  rw [he]
  exact input_contain 14 7 (by decide) v hb
def cl_14194 : CNF.NClause := [(14,true),(8,true),(566,false)]
theorem inp_14194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14194 = (containClause5 14 8) := by decide
  rw [he]
  exact input_contain 14 8 (by decide) v hb
def cl_14195 : CNF.NClause := [(14,true),(9,true),(567,false)]
theorem inp_14195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14195 = (containClause5 14 9) := by decide
  rw [he]
  exact input_contain 14 9 (by decide) v hb
def cl_14196 : CNF.NClause := [(14,true),(10,true),(568,false)]
theorem inp_14196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14196 = (containClause5 14 10) := by decide
  rw [he]
  exact input_contain 14 10 (by decide) v hb
def cl_14197 : CNF.NClause := [(14,true),(11,true),(569,false)]
theorem inp_14197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14197 = (containClause5 14 11) := by decide
  rw [he]
  exact input_contain 14 11 (by decide) v hb
def cl_14198 : CNF.NClause := [(14,true),(12,true),(570,false)]
theorem inp_14198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14198 = (containClause5 14 12) := by decide
  rw [he]
  exact input_contain 14 12 (by decide) v hb
def cl_14199 : CNF.NClause := [(14,true),(13,true),(571,false)]
theorem inp_14199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14199 = (containClause5 14 13) := by decide
  rw [he]
  exact input_contain 14 13 (by decide) v hb
def cl_14200 : CNF.NClause := [(14,true),(15,true),(573,false)]
theorem inp_14200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14200 = (containClause5 14 15) := by decide
  rw [he]
  exact input_contain 14 15 (by decide) v hb
def cl_14201 : CNF.NClause := [(14,true),(16,true),(574,false)]
theorem inp_14201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14201 = (containClause5 14 16) := by decide
  rw [he]
  exact input_contain 14 16 (by decide) v hb
def cl_14202 : CNF.NClause := [(14,true),(17,true),(575,false)]
theorem inp_14202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14202 = (containClause5 14 17) := by decide
  rw [he]
  exact input_contain 14 17 (by decide) v hb
def cl_14203 : CNF.NClause := [(14,true),(18,true),(576,false)]
theorem inp_14203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14203 = (containClause5 14 18) := by decide
  rw [he]
  exact input_contain 14 18 (by decide) v hb
def cl_14204 : CNF.NClause := [(14,true),(19,true),(577,false)]
theorem inp_14204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14204 = (containClause5 14 19) := by decide
  rw [he]
  exact input_contain 14 19 (by decide) v hb
end Percolation.NReplay
