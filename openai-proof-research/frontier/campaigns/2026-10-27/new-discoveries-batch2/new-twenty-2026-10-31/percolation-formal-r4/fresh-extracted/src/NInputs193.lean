import NInputs192
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12601 : CNF.NClause := [(868,true),(876,true),(879,true),(887,true),(890,false),(896,true)]
theorem inp_12601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 28) (closed_mem 24 28) cl_12601 (by decide) v hb
def cl_12602 : CNF.NClause := [(868,true),(876,true),(879,true),(887,false),(890,true),(896,true)]
theorem inp_12602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 28) (closed_mem 24 28) cl_12602 (by decide) v hb
def cl_12603 : CNF.NClause := [(868,true),(876,true),(879,false),(887,true),(890,true),(896,true)]
theorem inp_12603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 28) (closed_mem 24 28) cl_12603 (by decide) v hb
def cl_12604 : CNF.NClause := [(868,true),(876,false),(879,true),(887,true),(890,true),(896,true)]
theorem inp_12604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 28) (closed_mem 24 28) cl_12604 (by decide) v hb
def cl_12607 : CNF.NClause := [(868,true),(874,true),(880,true),(886,true),(892,false),(894,true)]
theorem inp_12607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 29) (closed_mem 24 29) cl_12607 (by decide) v hb
def cl_12613 : CNF.NClause := [(868,true),(873,true),(878,true),(883,true),(888,false),(893,true)]
theorem inp_12613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 30) (closed_mem 24 30) cl_12613 (by decide) v hb
def cl_12614 : CNF.NClause := [(868,true),(873,true),(878,true),(883,false),(888,true),(893,true)]
theorem inp_12614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 30) (closed_mem 24 30) cl_12614 (by decide) v hb
def cl_12615 : CNF.NClause := [(868,true),(873,true),(878,false),(883,true),(888,true),(893,true)]
theorem inp_12615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 30) (closed_mem 24 30) cl_12615 (by decide) v hb
def cl_12616 : CNF.NClause := [(868,true),(873,false),(878,true),(883,true),(888,true),(893,true)]
theorem inp_12616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 30) (closed_mem 24 30) cl_12616 (by decide) v hb
def cl_12623 : CNF.NClause := [(924,false),(925,true),(926,true),(927,true),(928,true),(929,true)]
theorem inp_12623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 0) (closed_mem 25 0) cl_12623 (by decide) v hb
def cl_12624 : CNF.NClause := [(903,true),(908,true),(913,true),(918,true),(923,true),(924,false)]
theorem inp_12624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 1) (closed_mem 25 1) cl_12624 (by decide) v hb
def cl_12630 : CNF.NClause := [(901,true),(906,true),(911,true),(916,true),(921,true),(924,false)]
theorem inp_12630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 2) (closed_mem 25 2) cl_12630 (by decide) v hb
def cl_12636 : CNF.NClause := [(902,true),(907,true),(912,true),(917,true),(922,true),(924,false)]
theorem inp_12636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 3) (closed_mem 25 3) cl_12636 (by decide) v hb
def cl_12642 : CNF.NClause := [(900,true),(905,true),(910,true),(915,true),(920,true),(924,false)]
theorem inp_12642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 4) (closed_mem 25 4) cl_12642 (by decide) v hb
def cl_12649 : CNF.NClause := [(919,true),(920,true),(921,true),(922,true),(923,false),(929,true)]
theorem inp_12649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 5) (closed_mem 25 5) cl_12649 (by decide) v hb
def cl_12650 : CNF.NClause := [(919,true),(920,true),(921,true),(922,false),(923,true),(929,true)]
theorem inp_12650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 5) (closed_mem 25 5) cl_12650 (by decide) v hb
def cl_12651 : CNF.NClause := [(919,true),(920,true),(921,false),(922,true),(923,true),(929,true)]
theorem inp_12651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 5) (closed_mem 25 5) cl_12651 (by decide) v hb
def cl_12652 : CNF.NClause := [(919,true),(920,false),(921,true),(922,true),(923,true),(929,true)]
theorem inp_12652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 5) (closed_mem 25 5) cl_12652 (by decide) v hb
def cl_12653 : CNF.NClause := [(919,false),(920,true),(921,true),(922,true),(923,true),(929,true)]
theorem inp_12653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 5) (closed_mem 25 5) cl_12653 (by decide) v hb
def cl_12654 : CNF.NClause := [(903,true),(907,true),(911,true),(915,true),(919,true),(928,false)]
theorem inp_12654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 6) (closed_mem 25 6) cl_12654 (by decide) v hb
def cl_12655 : CNF.NClause := [(903,true),(907,true),(911,true),(915,true),(919,false),(928,true)]
theorem inp_12655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 6) (closed_mem 25 6) cl_12655 (by decide) v hb
def cl_12656 : CNF.NClause := [(903,true),(907,true),(911,true),(915,false),(919,true),(928,true)]
theorem inp_12656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 6) (closed_mem 25 6) cl_12656 (by decide) v hb
def cl_12657 : CNF.NClause := [(903,true),(907,true),(911,false),(915,true),(919,true),(928,true)]
theorem inp_12657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 6) (closed_mem 25 6) cl_12657 (by decide) v hb
def cl_12658 : CNF.NClause := [(903,true),(907,false),(911,true),(915,true),(919,true),(928,true)]
theorem inp_12658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 6) (closed_mem 25 6) cl_12658 (by decide) v hb
def cl_12659 : CNF.NClause := [(903,false),(907,true),(911,true),(915,true),(919,true),(928,true)]
theorem inp_12659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 6) (closed_mem 25 6) cl_12659 (by decide) v hb
def cl_12660 : CNF.NClause := [(901,true),(908,true),(910,true),(917,true),(919,true),(926,false)]
theorem inp_12660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 7) (closed_mem 25 7) cl_12660 (by decide) v hb
def cl_12661 : CNF.NClause := [(901,true),(908,true),(910,true),(917,true),(919,false),(926,true)]
theorem inp_12661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 7) (closed_mem 25 7) cl_12661 (by decide) v hb
def cl_12662 : CNF.NClause := [(901,true),(908,true),(910,true),(917,false),(919,true),(926,true)]
theorem inp_12662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 7) (closed_mem 25 7) cl_12662 (by decide) v hb
def cl_12663 : CNF.NClause := [(901,true),(908,true),(910,false),(917,true),(919,true),(926,true)]
theorem inp_12663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 7) (closed_mem 25 7) cl_12663 (by decide) v hb
def cl_12664 : CNF.NClause := [(901,true),(908,false),(910,true),(917,true),(919,true),(926,true)]
theorem inp_12664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 7) (closed_mem 25 7) cl_12664 (by decide) v hb
def cl_12665 : CNF.NClause := [(901,false),(908,true),(910,true),(917,true),(919,true),(926,true)]
theorem inp_12665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 7) (closed_mem 25 7) cl_12665 (by decide) v hb
def cl_12666 : CNF.NClause := [(902,true),(905,true),(913,true),(916,true),(919,true),(927,false)]
theorem inp_12666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 8) (closed_mem 25 8) cl_12666 (by decide) v hb
def cl_12667 : CNF.NClause := [(902,true),(905,true),(913,true),(916,true),(919,false),(927,true)]
theorem inp_12667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 8) (closed_mem 25 8) cl_12667 (by decide) v hb
def cl_12668 : CNF.NClause := [(902,true),(905,true),(913,true),(916,false),(919,true),(927,true)]
theorem inp_12668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 8) (closed_mem 25 8) cl_12668 (by decide) v hb
def cl_12669 : CNF.NClause := [(902,true),(905,true),(913,false),(916,true),(919,true),(927,true)]
theorem inp_12669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 8) (closed_mem 25 8) cl_12669 (by decide) v hb
def cl_12670 : CNF.NClause := [(902,true),(905,false),(913,true),(916,true),(919,true),(927,true)]
theorem inp_12670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 8) (closed_mem 25 8) cl_12670 (by decide) v hb
def cl_12671 : CNF.NClause := [(902,false),(905,true),(913,true),(916,true),(919,true),(927,true)]
theorem inp_12671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 8) (closed_mem 25 8) cl_12671 (by decide) v hb
def cl_12672 : CNF.NClause := [(900,true),(906,true),(912,true),(918,true),(919,true),(925,false)]
theorem inp_12672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 9) (closed_mem 25 9) cl_12672 (by decide) v hb
def cl_12673 : CNF.NClause := [(900,true),(906,true),(912,true),(918,true),(919,false),(925,true)]
theorem inp_12673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 9) (closed_mem 25 9) cl_12673 (by decide) v hb
def cl_12674 : CNF.NClause := [(900,true),(906,true),(912,true),(918,false),(919,true),(925,true)]
theorem inp_12674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 9) (closed_mem 25 9) cl_12674 (by decide) v hb
def cl_12675 : CNF.NClause := [(900,true),(906,true),(912,false),(918,true),(919,true),(925,true)]
theorem inp_12675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 9) (closed_mem 25 9) cl_12675 (by decide) v hb
def cl_12676 : CNF.NClause := [(900,true),(906,false),(912,true),(918,true),(919,true),(925,true)]
theorem inp_12676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 9) (closed_mem 25 9) cl_12676 (by decide) v hb
def cl_12677 : CNF.NClause := [(900,false),(906,true),(912,true),(918,true),(919,true),(925,true)]
theorem inp_12677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 9) (closed_mem 25 9) cl_12677 (by decide) v hb
def cl_12679 : CNF.NClause := [(909,true),(910,true),(911,true),(912,true),(913,false),(929,true)]
theorem inp_12679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 10) (closed_mem 25 10) cl_12679 (by decide) v hb
def cl_12680 : CNF.NClause := [(909,true),(910,true),(911,true),(912,false),(913,true),(929,true)]
theorem inp_12680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 10) (closed_mem 25 10) cl_12680 (by decide) v hb
def cl_12681 : CNF.NClause := [(909,true),(910,true),(911,false),(912,true),(913,true),(929,true)]
theorem inp_12681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 10) (closed_mem 25 10) cl_12681 (by decide) v hb
def cl_12682 : CNF.NClause := [(909,true),(910,false),(911,true),(912,true),(913,true),(929,true)]
theorem inp_12682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 10) (closed_mem 25 10) cl_12682 (by decide) v hb
def cl_12683 : CNF.NClause := [(909,false),(910,true),(911,true),(912,true),(913,true),(929,true)]
theorem inp_12683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 10) (closed_mem 25 10) cl_12683 (by decide) v hb
def cl_12684 : CNF.NClause := [(903,true),(906,true),(909,true),(917,true),(920,true),(927,false)]
theorem inp_12684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 11) (closed_mem 25 11) cl_12684 (by decide) v hb
def cl_12685 : CNF.NClause := [(903,true),(906,true),(909,true),(917,true),(920,false),(927,true)]
theorem inp_12685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 11) (closed_mem 25 11) cl_12685 (by decide) v hb
end Percolation.NReplay
