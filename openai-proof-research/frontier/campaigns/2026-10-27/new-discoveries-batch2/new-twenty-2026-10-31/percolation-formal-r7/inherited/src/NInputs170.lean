import NInputs169
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10511 : CNF.NClause := [(532,false),(533,true),(534,true),(535,true),(536,true),(557,true)]
theorem inp_10511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 20) (closed_mem 13 20) cl_10511 (by decide) v hb
def cl_10515 : CNF.NClause := [(531,true),(532,true),(538,false),(544,true),(550,true),(553,true)]
theorem inp_10515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 21) (closed_mem 13 21) cl_10515 (by decide) v hb
def cl_10516 : CNF.NClause := [(531,true),(532,false),(538,true),(544,true),(550,true),(553,true)]
theorem inp_10516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 21) (closed_mem 13 21) cl_10516 (by decide) v hb
def cl_10517 : CNF.NClause := [(531,false),(532,true),(538,true),(544,true),(550,true),(553,true)]
theorem inp_10517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 21) (closed_mem 13 21) cl_10517 (by decide) v hb
def cl_10521 : CNF.NClause := [(529,true),(532,true),(540,false),(543,true),(551,true),(555,true)]
theorem inp_10521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 22) (closed_mem 13 22) cl_10521 (by decide) v hb
def cl_10527 : CNF.NClause := [(530,true),(532,true),(539,false),(546,true),(548,true),(554,true)]
theorem inp_10527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 23) (closed_mem 13 23) cl_10527 (by decide) v hb
def cl_10528 : CNF.NClause := [(530,true),(532,false),(539,true),(546,true),(548,true),(554,true)]
theorem inp_10528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 23) (closed_mem 13 23) cl_10528 (by decide) v hb
def cl_10529 : CNF.NClause := [(530,false),(532,true),(539,true),(546,true),(548,true),(554,true)]
theorem inp_10529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 23) (closed_mem 13 23) cl_10529 (by decide) v hb
def cl_10530 : CNF.NClause := [(528,true),(532,true),(541,true),(545,true),(549,true),(556,false)]
theorem inp_10530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 24) (closed_mem 13 24) cl_10530 (by decide) v hb
def cl_10533 : CNF.NClause := [(528,true),(532,true),(541,false),(545,true),(549,true),(556,true)]
theorem inp_10533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 24) (closed_mem 13 24) cl_10533 (by decide) v hb
def cl_10534 : CNF.NClause := [(528,true),(532,false),(541,true),(545,true),(549,true),(556,true)]
theorem inp_10534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 24) (closed_mem 13 24) cl_10534 (by decide) v hb
def cl_10535 : CNF.NClause := [(528,false),(532,true),(541,true),(545,true),(549,true),(556,true)]
theorem inp_10535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 24) (closed_mem 13 24) cl_10535 (by decide) v hb
def cl_10537 : CNF.NClause := [(527,true),(528,true),(529,true),(530,true),(531,false),(557,true)]
theorem inp_10537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 25) (closed_mem 13 25) cl_10537 (by decide) v hb
def cl_10538 : CNF.NClause := [(527,true),(528,true),(529,true),(530,false),(531,true),(557,true)]
theorem inp_10538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 25) (closed_mem 13 25) cl_10538 (by decide) v hb
def cl_10539 : CNF.NClause := [(527,true),(528,true),(529,false),(530,true),(531,true),(557,true)]
theorem inp_10539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 25) (closed_mem 13 25) cl_10539 (by decide) v hb
def cl_10540 : CNF.NClause := [(527,true),(528,false),(529,true),(530,true),(531,true),(557,true)]
theorem inp_10540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 25) (closed_mem 13 25) cl_10540 (by decide) v hb
def cl_10545 : CNF.NClause := [(527,true),(536,true),(540,false),(544,true),(548,true),(556,true)]
theorem inp_10545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 26) (closed_mem 13 26) cl_10545 (by decide) v hb
def cl_10548 : CNF.NClause := [(527,true),(534,true),(541,true),(543,true),(550,true),(554,false)]
theorem inp_10548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 27) (closed_mem 13 27) cl_10548 (by decide) v hb
def cl_10549 : CNF.NClause := [(527,true),(534,true),(541,true),(543,true),(550,false),(554,true)]
theorem inp_10549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 27) (closed_mem 13 27) cl_10549 (by decide) v hb
def cl_10550 : CNF.NClause := [(527,true),(534,true),(541,true),(543,false),(550,true),(554,true)]
theorem inp_10550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 27) (closed_mem 13 27) cl_10550 (by decide) v hb
def cl_10551 : CNF.NClause := [(527,true),(534,true),(541,false),(543,true),(550,true),(554,true)]
theorem inp_10551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 27) (closed_mem 13 27) cl_10551 (by decide) v hb
def cl_10552 : CNF.NClause := [(527,true),(534,false),(541,true),(543,true),(550,true),(554,true)]
theorem inp_10552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 27) (closed_mem 13 27) cl_10552 (by decide) v hb
def cl_10554 : CNF.NClause := [(527,true),(535,true),(538,true),(546,true),(549,true),(555,false)]
theorem inp_10554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 28) (closed_mem 13 28) cl_10554 (by decide) v hb
def cl_10555 : CNF.NClause := [(527,true),(535,true),(538,true),(546,true),(549,false),(555,true)]
theorem inp_10555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 28) (closed_mem 13 28) cl_10555 (by decide) v hb
def cl_10556 : CNF.NClause := [(527,true),(535,true),(538,true),(546,false),(549,true),(555,true)]
theorem inp_10556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 28) (closed_mem 13 28) cl_10556 (by decide) v hb
def cl_10557 : CNF.NClause := [(527,true),(535,true),(538,false),(546,true),(549,true),(555,true)]
theorem inp_10557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 28) (closed_mem 13 28) cl_10557 (by decide) v hb
def cl_10558 : CNF.NClause := [(527,true),(535,false),(538,true),(546,true),(549,true),(555,true)]
theorem inp_10558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 28) (closed_mem 13 28) cl_10558 (by decide) v hb
def cl_10560 : CNF.NClause := [(527,true),(533,true),(539,true),(545,true),(551,true),(553,false)]
theorem inp_10560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 29) (closed_mem 13 29) cl_10560 (by decide) v hb
def cl_10561 : CNF.NClause := [(527,true),(533,true),(539,true),(545,true),(551,false),(553,true)]
theorem inp_10561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 29) (closed_mem 13 29) cl_10561 (by decide) v hb
def cl_10562 : CNF.NClause := [(527,true),(533,true),(539,true),(545,false),(551,true),(553,true)]
theorem inp_10562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 29) (closed_mem 13 29) cl_10562 (by decide) v hb
def cl_10563 : CNF.NClause := [(527,true),(533,true),(539,false),(545,true),(551,true),(553,true)]
theorem inp_10563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 29) (closed_mem 13 29) cl_10563 (by decide) v hb
def cl_10564 : CNF.NClause := [(527,true),(533,false),(539,true),(545,true),(551,true),(553,true)]
theorem inp_10564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 29) (closed_mem 13 29) cl_10564 (by decide) v hb
def cl_10567 : CNF.NClause := [(527,true),(532,true),(537,true),(542,true),(547,false),(552,true)]
theorem inp_10567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 30) (closed_mem 13 30) cl_10567 (by decide) v hb
def cl_10568 : CNF.NClause := [(527,true),(532,true),(537,true),(542,false),(547,true),(552,true)]
theorem inp_10568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 30) (closed_mem 13 30) cl_10568 (by decide) v hb
def cl_10570 : CNF.NClause := [(527,true),(532,false),(537,true),(542,true),(547,true),(552,true)]
theorem inp_10570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 30) (closed_mem 13 30) cl_10570 (by decide) v hb
def cl_10573 : CNF.NClause := [(583,true),(584,true),(585,true),(586,true),(587,false),(588,true)]
theorem inp_10573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 0) (closed_mem 14 0) cl_10573 (by decide) v hb
def cl_10574 : CNF.NClause := [(583,true),(584,true),(585,true),(586,false),(587,true),(588,true)]
theorem inp_10574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 0) (closed_mem 14 0) cl_10574 (by decide) v hb
def cl_10575 : CNF.NClause := [(583,true),(584,true),(585,false),(586,true),(587,true),(588,true)]
theorem inp_10575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 0) (closed_mem 14 0) cl_10575 (by decide) v hb
def cl_10576 : CNF.NClause := [(583,true),(584,false),(585,true),(586,true),(587,true),(588,true)]
theorem inp_10576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 0) (closed_mem 14 0) cl_10576 (by decide) v hb
def cl_10581 : CNF.NClause := [(562,true),(567,true),(572,false),(577,true),(582,true),(583,true)]
theorem inp_10581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 1) (closed_mem 14 1) cl_10581 (by decide) v hb
def cl_10585 : CNF.NClause := [(560,true),(565,true),(570,true),(575,true),(580,false),(583,true)]
theorem inp_10585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 2) (closed_mem 14 2) cl_10585 (by decide) v hb
def cl_10586 : CNF.NClause := [(560,true),(565,true),(570,true),(575,false),(580,true),(583,true)]
theorem inp_10586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 2) (closed_mem 14 2) cl_10586 (by decide) v hb
def cl_10587 : CNF.NClause := [(560,true),(565,true),(570,false),(575,true),(580,true),(583,true)]
theorem inp_10587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 2) (closed_mem 14 2) cl_10587 (by decide) v hb
def cl_10588 : CNF.NClause := [(560,true),(565,false),(570,true),(575,true),(580,true),(583,true)]
theorem inp_10588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 2) (closed_mem 14 2) cl_10588 (by decide) v hb
def cl_10589 : CNF.NClause := [(560,false),(565,true),(570,true),(575,true),(580,true),(583,true)]
theorem inp_10589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 2) (closed_mem 14 2) cl_10589 (by decide) v hb
def cl_10591 : CNF.NClause := [(561,true),(566,true),(571,true),(576,true),(581,false),(583,true)]
theorem inp_10591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 3) (closed_mem 14 3) cl_10591 (by decide) v hb
def cl_10592 : CNF.NClause := [(561,true),(566,true),(571,true),(576,false),(581,true),(583,true)]
theorem inp_10592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 3) (closed_mem 14 3) cl_10592 (by decide) v hb
def cl_10593 : CNF.NClause := [(561,true),(566,true),(571,false),(576,true),(581,true),(583,true)]
theorem inp_10593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 3) (closed_mem 14 3) cl_10593 (by decide) v hb
def cl_10594 : CNF.NClause := [(561,true),(566,false),(571,true),(576,true),(581,true),(583,true)]
theorem inp_10594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 3) (closed_mem 14 3) cl_10594 (by decide) v hb
def cl_10595 : CNF.NClause := [(561,false),(566,true),(571,true),(576,true),(581,true),(583,true)]
theorem inp_10595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 3) (closed_mem 14 3) cl_10595 (by decide) v hb
end Percolation.NReplay
