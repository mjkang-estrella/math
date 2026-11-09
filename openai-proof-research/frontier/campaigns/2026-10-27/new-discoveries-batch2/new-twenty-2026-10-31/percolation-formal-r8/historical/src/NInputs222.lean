import NInputs221
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14505 : CNF.NClause := [(24,true),(19,true),(887,false)]
theorem inp_14505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14505 = (containClause5 24 19) := by decide
  rw [he]
  exact input_contain 24 19 (by decide) v hb
def cl_14506 : CNF.NClause := [(24,true),(20,true),(888,false)]
theorem inp_14506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14506 = (containClause5 24 20) := by decide
  rw [he]
  exact input_contain 24 20 (by decide) v hb
def cl_14507 : CNF.NClause := [(24,true),(21,true),(889,false)]
theorem inp_14507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14507 = (containClause5 24 21) := by decide
  rw [he]
  exact input_contain 24 21 (by decide) v hb
def cl_14508 : CNF.NClause := [(24,true),(22,true),(890,false)]
theorem inp_14508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14508 = (containClause5 24 22) := by decide
  rw [he]
  exact input_contain 24 22 (by decide) v hb
def cl_14509 : CNF.NClause := [(24,true),(23,true),(891,false)]
theorem inp_14509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14509 = (containClause5 24 23) := by decide
  rw [he]
  exact input_contain 24 23 (by decide) v hb
def cl_14510 : CNF.NClause := [(24,true),(25,true),(893,false)]
theorem inp_14510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14510 = (containClause5 24 25) := by decide
  rw [he]
  exact input_contain 24 25 (by decide) v hb
def cl_14511 : CNF.NClause := [(24,true),(26,true),(894,false)]
theorem inp_14511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14511 = (containClause5 24 26) := by decide
  rw [he]
  exact input_contain 24 26 (by decide) v hb
def cl_14512 : CNF.NClause := [(24,true),(27,true),(895,false)]
theorem inp_14512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14512 = (containClause5 24 27) := by decide
  rw [he]
  exact input_contain 24 27 (by decide) v hb
def cl_14513 : CNF.NClause := [(24,true),(28,true),(896,false)]
theorem inp_14513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14513 = (containClause5 24 28) := by decide
  rw [he]
  exact input_contain 24 28 (by decide) v hb
def cl_14514 : CNF.NClause := [(24,true),(29,true),(897,false)]
theorem inp_14514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14514 = (containClause5 24 29) := by decide
  rw [he]
  exact input_contain 24 29 (by decide) v hb
def cl_14515 : CNF.NClause := [(24,true),(30,true),(898,false)]
theorem inp_14515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14515 = (containClause5 24 30) := by decide
  rw [he]
  exact input_contain 24 30 (by decide) v hb
def cl_14516 : CNF.NClause := [(25,true),(0,true),(899,false)]
theorem inp_14516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14516 = (containClause5 25 0) := by decide
  rw [he]
  exact input_contain 25 0 (by decide) v hb
def cl_14517 : CNF.NClause := [(25,true),(1,true),(900,false)]
theorem inp_14517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14517 = (containClause5 25 1) := by decide
  rw [he]
  exact input_contain 25 1 (by decide) v hb
def cl_14518 : CNF.NClause := [(25,true),(2,true),(901,false)]
theorem inp_14518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14518 = (containClause5 25 2) := by decide
  rw [he]
  exact input_contain 25 2 (by decide) v hb
def cl_14519 : CNF.NClause := [(25,true),(3,true),(902,false)]
theorem inp_14519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14519 = (containClause5 25 3) := by decide
  rw [he]
  exact input_contain 25 3 (by decide) v hb
def cl_14520 : CNF.NClause := [(25,true),(4,true),(903,false)]
theorem inp_14520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14520 = (containClause5 25 4) := by decide
  rw [he]
  exact input_contain 25 4 (by decide) v hb
def cl_14521 : CNF.NClause := [(25,true),(5,true),(904,false)]
theorem inp_14521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14521 = (containClause5 25 5) := by decide
  rw [he]
  exact input_contain 25 5 (by decide) v hb
def cl_14522 : CNF.NClause := [(25,true),(6,true),(905,false)]
theorem inp_14522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14522 = (containClause5 25 6) := by decide
  rw [he]
  exact input_contain 25 6 (by decide) v hb
def cl_14523 : CNF.NClause := [(25,true),(7,true),(906,false)]
theorem inp_14523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14523 = (containClause5 25 7) := by decide
  rw [he]
  exact input_contain 25 7 (by decide) v hb
def cl_14524 : CNF.NClause := [(25,true),(8,true),(907,false)]
theorem inp_14524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14524 = (containClause5 25 8) := by decide
  rw [he]
  exact input_contain 25 8 (by decide) v hb
def cl_14525 : CNF.NClause := [(25,true),(9,true),(908,false)]
theorem inp_14525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14525 = (containClause5 25 9) := by decide
  rw [he]
  exact input_contain 25 9 (by decide) v hb
def cl_14526 : CNF.NClause := [(25,true),(10,true),(909,false)]
theorem inp_14526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14526 = (containClause5 25 10) := by decide
  rw [he]
  exact input_contain 25 10 (by decide) v hb
def cl_14527 : CNF.NClause := [(25,true),(11,true),(910,false)]
theorem inp_14527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14527 = (containClause5 25 11) := by decide
  rw [he]
  exact input_contain 25 11 (by decide) v hb
def cl_14528 : CNF.NClause := [(25,true),(12,true),(911,false)]
theorem inp_14528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14528 = (containClause5 25 12) := by decide
  rw [he]
  exact input_contain 25 12 (by decide) v hb
def cl_14529 : CNF.NClause := [(25,true),(13,true),(912,false)]
theorem inp_14529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14529 = (containClause5 25 13) := by decide
  rw [he]
  exact input_contain 25 13 (by decide) v hb
def cl_14530 : CNF.NClause := [(25,true),(14,true),(913,false)]
theorem inp_14530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14530 = (containClause5 25 14) := by decide
  rw [he]
  exact input_contain 25 14 (by decide) v hb
def cl_14531 : CNF.NClause := [(25,true),(15,true),(914,false)]
theorem inp_14531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14531 = (containClause5 25 15) := by decide
  rw [he]
  exact input_contain 25 15 (by decide) v hb
def cl_14532 : CNF.NClause := [(25,true),(16,true),(915,false)]
theorem inp_14532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14532 = (containClause5 25 16) := by decide
  rw [he]
  exact input_contain 25 16 (by decide) v hb
def cl_14533 : CNF.NClause := [(25,true),(17,true),(916,false)]
theorem inp_14533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14533 = (containClause5 25 17) := by decide
  rw [he]
  exact input_contain 25 17 (by decide) v hb
def cl_14534 : CNF.NClause := [(25,true),(18,true),(917,false)]
theorem inp_14534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14534 = (containClause5 25 18) := by decide
  rw [he]
  exact input_contain 25 18 (by decide) v hb
def cl_14535 : CNF.NClause := [(25,true),(19,true),(918,false)]
theorem inp_14535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14535 = (containClause5 25 19) := by decide
  rw [he]
  exact input_contain 25 19 (by decide) v hb
def cl_14536 : CNF.NClause := [(25,true),(20,true),(919,false)]
theorem inp_14536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14536 = (containClause5 25 20) := by decide
  rw [he]
  exact input_contain 25 20 (by decide) v hb
def cl_14537 : CNF.NClause := [(25,true),(21,true),(920,false)]
theorem inp_14537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14537 = (containClause5 25 21) := by decide
  rw [he]
  exact input_contain 25 21 (by decide) v hb
def cl_14538 : CNF.NClause := [(25,true),(22,true),(921,false)]
theorem inp_14538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14538 = (containClause5 25 22) := by decide
  rw [he]
  exact input_contain 25 22 (by decide) v hb
def cl_14539 : CNF.NClause := [(25,true),(23,true),(922,false)]
theorem inp_14539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14539 = (containClause5 25 23) := by decide
  rw [he]
  exact input_contain 25 23 (by decide) v hb
def cl_14540 : CNF.NClause := [(25,true),(24,true),(923,false)]
theorem inp_14540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14540 = (containClause5 25 24) := by decide
  rw [he]
  exact input_contain 25 24 (by decide) v hb
def cl_14541 : CNF.NClause := [(25,true),(26,true),(925,false)]
theorem inp_14541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14541 = (containClause5 25 26) := by decide
  rw [he]
  exact input_contain 25 26 (by decide) v hb
def cl_14542 : CNF.NClause := [(25,true),(27,true),(926,false)]
theorem inp_14542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14542 = (containClause5 25 27) := by decide
  rw [he]
  exact input_contain 25 27 (by decide) v hb
def cl_14543 : CNF.NClause := [(25,true),(28,true),(927,false)]
theorem inp_14543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14543 = (containClause5 25 28) := by decide
  rw [he]
  exact input_contain 25 28 (by decide) v hb
def cl_14544 : CNF.NClause := [(25,true),(29,true),(928,false)]
theorem inp_14544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14544 = (containClause5 25 29) := by decide
  rw [he]
  exact input_contain 25 29 (by decide) v hb
def cl_14545 : CNF.NClause := [(25,true),(30,true),(929,false)]
theorem inp_14545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14545 = (containClause5 25 30) := by decide
  rw [he]
  exact input_contain 25 30 (by decide) v hb
def cl_14546 : CNF.NClause := [(26,true),(0,true),(930,false)]
theorem inp_14546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14546 = (containClause5 26 0) := by decide
  rw [he]
  exact input_contain 26 0 (by decide) v hb
def cl_14547 : CNF.NClause := [(26,true),(1,true),(931,false)]
theorem inp_14547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14547 = (containClause5 26 1) := by decide
  rw [he]
  exact input_contain 26 1 (by decide) v hb
def cl_14548 : CNF.NClause := [(26,true),(2,true),(932,false)]
theorem inp_14548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14548 = (containClause5 26 2) := by decide
  rw [he]
  exact input_contain 26 2 (by decide) v hb
def cl_14549 : CNF.NClause := [(26,true),(3,true),(933,false)]
theorem inp_14549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14549 = (containClause5 26 3) := by decide
  rw [he]
  exact input_contain 26 3 (by decide) v hb
def cl_14550 : CNF.NClause := [(26,true),(4,true),(934,false)]
theorem inp_14550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14550 = (containClause5 26 4) := by decide
  rw [he]
  exact input_contain 26 4 (by decide) v hb
def cl_14551 : CNF.NClause := [(26,true),(5,true),(935,false)]
theorem inp_14551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14551 = (containClause5 26 5) := by decide
  rw [he]
  exact input_contain 26 5 (by decide) v hb
def cl_14552 : CNF.NClause := [(26,true),(6,true),(936,false)]
theorem inp_14552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14552 = (containClause5 26 6) := by decide
  rw [he]
  exact input_contain 26 6 (by decide) v hb
def cl_14553 : CNF.NClause := [(26,true),(7,true),(937,false)]
theorem inp_14553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14553 = (containClause5 26 7) := by decide
  rw [he]
  exact input_contain 26 7 (by decide) v hb
def cl_14554 : CNF.NClause := [(26,true),(8,true),(938,false)]
theorem inp_14554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14554 = (containClause5 26 8) := by decide
  rw [he]
  exact input_contain 26 8 (by decide) v hb
end Percolation.NReplay
