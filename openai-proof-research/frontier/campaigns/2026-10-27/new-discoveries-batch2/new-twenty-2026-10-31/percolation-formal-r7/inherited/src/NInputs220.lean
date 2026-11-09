import NInputs219
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14405 : CNF.NClause := [(21,true),(9,true),(784,false)]
theorem inp_14405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14405 = (containClause5 21 9) := by decide
  rw [he]
  exact input_contain 21 9 (by decide) v hb
def cl_14406 : CNF.NClause := [(21,true),(10,true),(785,false)]
theorem inp_14406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14406 v hb
def cl_14407 : CNF.NClause := [(21,true),(11,true),(786,false)]
theorem inp_14407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14407 v hb
def cl_14408 : CNF.NClause := [(21,true),(12,true),(787,false)]
theorem inp_14408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14408 = (containClause5 21 12) := by decide
  rw [he]
  exact input_contain 21 12 (by decide) v hb
def cl_14409 : CNF.NClause := [(21,true),(13,true),(788,false)]
theorem inp_14409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14409 = (containClause5 21 13) := by decide
  rw [he]
  exact input_contain 21 13 (by decide) v hb
def cl_14410 : CNF.NClause := [(21,true),(14,true),(789,false)]
theorem inp_14410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14410 = (containClause5 21 14) := by decide
  rw [he]
  exact input_contain 21 14 (by decide) v hb
def cl_14411 : CNF.NClause := [(21,true),(15,true),(790,false)]
theorem inp_14411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14411 = (containClause5 21 15) := by decide
  rw [he]
  exact input_contain 21 15 (by decide) v hb
def cl_14412 : CNF.NClause := [(21,true),(16,true),(791,false)]
theorem inp_14412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14412 v hb
def cl_14413 : CNF.NClause := [(21,true),(17,true),(792,false)]
theorem inp_14413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14413 v hb
def cl_14414 : CNF.NClause := [(21,true),(18,true),(793,false)]
theorem inp_14414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14414 = (containClause5 21 18) := by decide
  rw [he]
  exact input_contain 21 18 (by decide) v hb
def cl_14415 : CNF.NClause := [(21,true),(19,true),(794,false)]
theorem inp_14415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14415 v hb
def cl_14416 : CNF.NClause := [(21,true),(20,true),(795,false)]
theorem inp_14416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14416 = (containClause5 21 20) := by decide
  rw [he]
  exact input_contain 21 20 (by decide) v hb
def cl_14417 : CNF.NClause := [(21,true),(22,true),(797,false)]
theorem inp_14417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14417 v hb
def cl_14418 : CNF.NClause := [(21,true),(23,true),(798,false)]
theorem inp_14418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14418 = (containClause5 21 23) := by decide
  rw [he]
  exact input_contain 21 23 (by decide) v hb
def cl_14419 : CNF.NClause := [(21,true),(24,true),(799,false)]
theorem inp_14419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14419 v hb
def cl_14420 : CNF.NClause := [(21,true),(25,true),(800,false)]
theorem inp_14420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14420 v hb
def cl_14421 : CNF.NClause := [(21,true),(26,true),(801,false)]
theorem inp_14421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14421 = (containClause5 21 26) := by decide
  rw [he]
  exact input_contain 21 26 (by decide) v hb
def cl_14422 : CNF.NClause := [(21,true),(27,true),(802,false)]
theorem inp_14422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14422 v hb
def cl_14423 : CNF.NClause := [(21,true),(28,true),(803,false)]
theorem inp_14423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14423 v hb
def cl_14424 : CNF.NClause := [(21,true),(29,true),(804,false)]
theorem inp_14424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14424 = (containClause5 21 29) := by decide
  rw [he]
  exact input_contain 21 29 (by decide) v hb
def cl_14425 : CNF.NClause := [(21,true),(30,true),(805,false)]
theorem inp_14425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14425 = (containClause5 21 30) := by decide
  rw [he]
  exact input_contain 21 30 (by decide) v hb
def cl_14426 : CNF.NClause := [(22,true),(0,true),(806,false)]
theorem inp_14426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14426 = (containClause5 22 0) := by decide
  rw [he]
  exact input_contain 22 0 (by decide) v hb
def cl_14427 : CNF.NClause := [(22,true),(1,true),(807,false)]
theorem inp_14427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14427 = (containClause5 22 1) := by decide
  rw [he]
  exact input_contain 22 1 (by decide) v hb
def cl_14428 : CNF.NClause := [(22,true),(2,true),(808,false)]
theorem inp_14428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14428 v hb
def cl_14429 : CNF.NClause := [(22,true),(3,true),(809,false)]
theorem inp_14429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14429 = (containClause5 22 3) := by decide
  rw [he]
  exact input_contain 22 3 (by decide) v hb
def cl_14430 : CNF.NClause := [(22,true),(4,true),(810,false)]
theorem inp_14430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14430 = (containClause5 22 4) := by decide
  rw [he]
  exact input_contain 22 4 (by decide) v hb
def cl_14431 : CNF.NClause := [(22,true),(5,true),(811,false)]
theorem inp_14431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14431 = (containClause5 22 5) := by decide
  rw [he]
  exact input_contain 22 5 (by decide) v hb
def cl_14432 : CNF.NClause := [(22,true),(6,true),(812,false)]
theorem inp_14432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14432 v hb
def cl_14433 : CNF.NClause := [(22,true),(7,true),(813,false)]
theorem inp_14433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14433 = (containClause5 22 7) := by decide
  rw [he]
  exact input_contain 22 7 (by decide) v hb
def cl_14434 : CNF.NClause := [(22,true),(8,true),(814,false)]
theorem inp_14434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14434 = (containClause5 22 8) := by decide
  rw [he]
  exact input_contain 22 8 (by decide) v hb
def cl_14435 : CNF.NClause := [(22,true),(9,true),(815,false)]
theorem inp_14435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14435 = (containClause5 22 9) := by decide
  rw [he]
  exact input_contain 22 9 (by decide) v hb
def cl_14436 : CNF.NClause := [(22,true),(10,true),(816,false)]
theorem inp_14436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14436 v hb
def cl_14437 : CNF.NClause := [(22,true),(11,true),(817,false)]
theorem inp_14437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14437 = (containClause5 22 11) := by decide
  rw [he]
  exact input_contain 22 11 (by decide) v hb
def cl_14438 : CNF.NClause := [(22,true),(12,true),(818,false)]
theorem inp_14438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14438 = (containClause5 22 12) := by decide
  rw [he]
  exact input_contain 22 12 (by decide) v hb
def cl_14439 : CNF.NClause := [(22,true),(13,true),(819,false)]
theorem inp_14439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14439 = (containClause5 22 13) := by decide
  rw [he]
  exact input_contain 22 13 (by decide) v hb
def cl_14440 : CNF.NClause := [(22,true),(14,true),(820,false)]
theorem inp_14440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14440 = (containClause5 22 14) := by decide
  rw [he]
  exact input_contain 22 14 (by decide) v hb
def cl_14441 : CNF.NClause := [(22,true),(15,true),(821,false)]
theorem inp_14441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14441 = (containClause5 22 15) := by decide
  rw [he]
  exact input_contain 22 15 (by decide) v hb
def cl_14442 : CNF.NClause := [(22,true),(16,true),(822,false)]
theorem inp_14442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14442 = (containClause5 22 16) := by decide
  rw [he]
  exact input_contain 22 16 (by decide) v hb
def cl_14443 : CNF.NClause := [(22,true),(17,true),(823,false)]
theorem inp_14443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14443 = (containClause5 22 17) := by decide
  rw [he]
  exact input_contain 22 17 (by decide) v hb
def cl_14444 : CNF.NClause := [(22,true),(18,true),(824,false)]
theorem inp_14444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14444 = (containClause5 22 18) := by decide
  rw [he]
  exact input_contain 22 18 (by decide) v hb
def cl_14445 : CNF.NClause := [(22,true),(19,true),(825,false)]
theorem inp_14445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14445 v hb
def cl_14446 : CNF.NClause := [(22,true),(20,true),(826,false)]
theorem inp_14446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14446 v hb
def cl_14447 : CNF.NClause := [(22,true),(21,true),(827,false)]
theorem inp_14447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14447 v hb
def cl_14448 : CNF.NClause := [(22,true),(23,true),(829,false)]
theorem inp_14448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14448 = (containClause5 22 23) := by decide
  rw [he]
  exact input_contain 22 23 (by decide) v hb
def cl_14449 : CNF.NClause := [(22,true),(24,true),(830,false)]
theorem inp_14449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14449 v hb
def cl_14450 : CNF.NClause := [(22,true),(25,true),(831,false)]
theorem inp_14450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14450 = (containClause5 22 25) := by decide
  rw [he]
  exact input_contain 22 25 (by decide) v hb
def cl_14451 : CNF.NClause := [(22,true),(26,true),(832,false)]
theorem inp_14451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14451 = (containClause5 22 26) := by decide
  rw [he]
  exact input_contain 22 26 (by decide) v hb
def cl_14452 : CNF.NClause := [(22,true),(27,true),(833,false)]
theorem inp_14452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14452 = (containClause5 22 27) := by decide
  rw [he]
  exact input_contain 22 27 (by decide) v hb
def cl_14453 : CNF.NClause := [(22,true),(28,true),(834,false)]
theorem inp_14453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14453 = (containClause5 22 28) := by decide
  rw [he]
  exact input_contain 22 28 (by decide) v hb
def cl_14454 : CNF.NClause := [(22,true),(29,true),(835,false)]
theorem inp_14454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14454 v hb
end Percolation.NReplay
