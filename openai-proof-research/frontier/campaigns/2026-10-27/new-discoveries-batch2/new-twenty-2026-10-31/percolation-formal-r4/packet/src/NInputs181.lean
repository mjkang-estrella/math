import NInputs180
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11486 : CNF.NClause := [(682,true),(690,true),(693,true),(701,false),(704,true),(710,true)]
theorem inp_11486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 28) (closed_mem 18 28) cl_11486 (by decide) v hb
def cl_11487 : CNF.NClause := [(682,true),(690,true),(693,false),(701,true),(704,true),(710,true)]
theorem inp_11487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 28) (closed_mem 18 28) cl_11487 (by decide) v hb
def cl_11488 : CNF.NClause := [(682,true),(690,false),(693,true),(701,true),(704,true),(710,true)]
theorem inp_11488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 28) (closed_mem 18 28) cl_11488 (by decide) v hb
def cl_11492 : CNF.NClause := [(682,true),(688,true),(694,true),(700,false),(706,true),(708,true)]
theorem inp_11492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 29) (closed_mem 18 29) cl_11492 (by decide) v hb
def cl_11497 : CNF.NClause := [(682,true),(687,true),(692,true),(697,true),(702,false),(707,true)]
theorem inp_11497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 30) (closed_mem 18 30) cl_11497 (by decide) v hb
def cl_11498 : CNF.NClause := [(682,true),(687,true),(692,true),(697,false),(702,true),(707,true)]
theorem inp_11498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 30) (closed_mem 18 30) cl_11498 (by decide) v hb
def cl_11499 : CNF.NClause := [(682,true),(687,true),(692,false),(697,true),(702,true),(707,true)]
theorem inp_11499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 30) (closed_mem 18 30) cl_11499 (by decide) v hb
def cl_11500 : CNF.NClause := [(682,true),(687,false),(692,true),(697,true),(702,true),(707,true)]
theorem inp_11500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 30) (closed_mem 18 30) cl_11500 (by decide) v hb
def cl_11503 : CNF.NClause := [(738,true),(739,true),(740,true),(741,true),(742,false),(743,true)]
theorem inp_11503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 0) (closed_mem 19 0) cl_11503 (by decide) v hb
def cl_11504 : CNF.NClause := [(738,true),(739,true),(740,true),(741,false),(742,true),(743,true)]
theorem inp_11504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 0) (closed_mem 19 0) cl_11504 (by decide) v hb
def cl_11505 : CNF.NClause := [(738,true),(739,true),(740,false),(741,true),(742,true),(743,true)]
theorem inp_11505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 0) (closed_mem 19 0) cl_11505 (by decide) v hb
def cl_11506 : CNF.NClause := [(738,true),(739,false),(740,true),(741,true),(742,true),(743,true)]
theorem inp_11506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 0) (closed_mem 19 0) cl_11506 (by decide) v hb
def cl_11510 : CNF.NClause := [(717,true),(722,true),(727,true),(732,false),(737,true),(738,true)]
theorem inp_11510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 1) (closed_mem 19 1) cl_11510 (by decide) v hb
def cl_11515 : CNF.NClause := [(715,true),(720,true),(725,true),(730,true),(735,false),(738,true)]
theorem inp_11515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 2) (closed_mem 19 2) cl_11515 (by decide) v hb
def cl_11516 : CNF.NClause := [(715,true),(720,true),(725,true),(730,false),(735,true),(738,true)]
theorem inp_11516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 2) (closed_mem 19 2) cl_11516 (by decide) v hb
def cl_11517 : CNF.NClause := [(715,true),(720,true),(725,false),(730,true),(735,true),(738,true)]
theorem inp_11517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 2) (closed_mem 19 2) cl_11517 (by decide) v hb
def cl_11519 : CNF.NClause := [(715,false),(720,true),(725,true),(730,true),(735,true),(738,true)]
theorem inp_11519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 2) (closed_mem 19 2) cl_11519 (by decide) v hb
def cl_11521 : CNF.NClause := [(716,true),(721,true),(726,true),(731,true),(736,false),(738,true)]
theorem inp_11521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 3) (closed_mem 19 3) cl_11521 (by decide) v hb
def cl_11523 : CNF.NClause := [(716,true),(721,true),(726,false),(731,true),(736,true),(738,true)]
theorem inp_11523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 3) (closed_mem 19 3) cl_11523 (by decide) v hb
def cl_11524 : CNF.NClause := [(716,true),(721,false),(726,true),(731,true),(736,true),(738,true)]
theorem inp_11524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 3) (closed_mem 19 3) cl_11524 (by decide) v hb
def cl_11525 : CNF.NClause := [(716,false),(721,true),(726,true),(731,true),(736,true),(738,true)]
theorem inp_11525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 3) (closed_mem 19 3) cl_11525 (by decide) v hb
def cl_11528 : CNF.NClause := [(714,true),(719,true),(724,true),(729,false),(734,true),(738,true)]
theorem inp_11528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 4) (closed_mem 19 4) cl_11528 (by decide) v hb
def cl_11529 : CNF.NClause := [(714,true),(719,true),(724,false),(729,true),(734,true),(738,true)]
theorem inp_11529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 4) (closed_mem 19 4) cl_11529 (by decide) v hb
def cl_11530 : CNF.NClause := [(714,true),(719,false),(724,true),(729,true),(734,true),(738,true)]
theorem inp_11530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 4) (closed_mem 19 4) cl_11530 (by decide) v hb
def cl_11531 : CNF.NClause := [(714,false),(719,true),(724,true),(729,true),(734,true),(738,true)]
theorem inp_11531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 4) (closed_mem 19 4) cl_11531 (by decide) v hb
def cl_11533 : CNF.NClause := [(733,true),(734,true),(735,true),(736,true),(737,false),(743,true)]
theorem inp_11533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 5) (closed_mem 19 5) cl_11533 (by decide) v hb
def cl_11534 : CNF.NClause := [(733,true),(734,true),(735,true),(736,false),(737,true),(743,true)]
theorem inp_11534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 5) (closed_mem 19 5) cl_11534 (by decide) v hb
def cl_11535 : CNF.NClause := [(733,true),(734,true),(735,false),(736,true),(737,true),(743,true)]
theorem inp_11535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 5) (closed_mem 19 5) cl_11535 (by decide) v hb
def cl_11537 : CNF.NClause := [(733,false),(734,true),(735,true),(736,true),(737,true),(743,true)]
theorem inp_11537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 5) (closed_mem 19 5) cl_11537 (by decide) v hb
def cl_11539 : CNF.NClause := [(717,true),(721,true),(725,true),(729,true),(733,false),(742,true)]
theorem inp_11539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 6) (closed_mem 19 6) cl_11539 (by decide) v hb
def cl_11540 : CNF.NClause := [(717,true),(721,true),(725,true),(729,false),(733,true),(742,true)]
theorem inp_11540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 6) (closed_mem 19 6) cl_11540 (by decide) v hb
def cl_11541 : CNF.NClause := [(717,true),(721,true),(725,false),(729,true),(733,true),(742,true)]
theorem inp_11541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 6) (closed_mem 19 6) cl_11541 (by decide) v hb
def cl_11542 : CNF.NClause := [(717,true),(721,false),(725,true),(729,true),(733,true),(742,true)]
theorem inp_11542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 6) (closed_mem 19 6) cl_11542 (by decide) v hb
def cl_11543 : CNF.NClause := [(717,false),(721,true),(725,true),(729,true),(733,true),(742,true)]
theorem inp_11543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 6) (closed_mem 19 6) cl_11543 (by decide) v hb
def cl_11544 : CNF.NClause := [(715,true),(722,true),(724,true),(731,true),(733,true),(740,false)]
theorem inp_11544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 7) (closed_mem 19 7) cl_11544 (by decide) v hb
def cl_11545 : CNF.NClause := [(715,true),(722,true),(724,true),(731,true),(733,false),(740,true)]
theorem inp_11545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 7) (closed_mem 19 7) cl_11545 (by decide) v hb
def cl_11546 : CNF.NClause := [(715,true),(722,true),(724,true),(731,false),(733,true),(740,true)]
theorem inp_11546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 7) (closed_mem 19 7) cl_11546 (by decide) v hb
def cl_11547 : CNF.NClause := [(715,true),(722,true),(724,false),(731,true),(733,true),(740,true)]
theorem inp_11547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 7) (closed_mem 19 7) cl_11547 (by decide) v hb
def cl_11548 : CNF.NClause := [(715,true),(722,false),(724,true),(731,true),(733,true),(740,true)]
theorem inp_11548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 7) (closed_mem 19 7) cl_11548 (by decide) v hb
def cl_11549 : CNF.NClause := [(715,false),(722,true),(724,true),(731,true),(733,true),(740,true)]
theorem inp_11549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 7) (closed_mem 19 7) cl_11549 (by decide) v hb
def cl_11550 : CNF.NClause := [(716,true),(719,true),(727,true),(730,true),(733,true),(741,false)]
theorem inp_11550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 8) (closed_mem 19 8) cl_11550 (by decide) v hb
def cl_11551 : CNF.NClause := [(716,true),(719,true),(727,true),(730,true),(733,false),(741,true)]
theorem inp_11551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 8) (closed_mem 19 8) cl_11551 (by decide) v hb
def cl_11553 : CNF.NClause := [(716,true),(719,true),(727,false),(730,true),(733,true),(741,true)]
theorem inp_11553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 8) (closed_mem 19 8) cl_11553 (by decide) v hb
def cl_11554 : CNF.NClause := [(716,true),(719,false),(727,true),(730,true),(733,true),(741,true)]
theorem inp_11554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 8) (closed_mem 19 8) cl_11554 (by decide) v hb
def cl_11555 : CNF.NClause := [(716,false),(719,true),(727,true),(730,true),(733,true),(741,true)]
theorem inp_11555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 8) (closed_mem 19 8) cl_11555 (by decide) v hb
def cl_11558 : CNF.NClause := [(714,true),(720,true),(726,true),(732,false),(733,true),(739,true)]
theorem inp_11558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 9) (closed_mem 19 9) cl_11558 (by decide) v hb
def cl_11563 : CNF.NClause := [(723,true),(724,true),(725,true),(726,true),(727,false),(743,true)]
theorem inp_11563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 10) (closed_mem 19 10) cl_11563 (by decide) v hb
def cl_11564 : CNF.NClause := [(723,true),(724,true),(725,true),(726,false),(727,true),(743,true)]
theorem inp_11564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 10) (closed_mem 19 10) cl_11564 (by decide) v hb
def cl_11565 : CNF.NClause := [(723,true),(724,true),(725,false),(726,true),(727,true),(743,true)]
theorem inp_11565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11565 v hb
def cl_11566 : CNF.NClause := [(723,true),(724,false),(725,true),(726,true),(727,true),(743,true)]
theorem inp_11566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 10) (closed_mem 19 10) cl_11566 (by decide) v hb
end Percolation.NReplay
