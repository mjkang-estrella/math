import NInputs181
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11567 : CNF.NClause := [(723,false),(724,true),(725,true),(726,true),(727,true),(743,true)]
theorem inp_11567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 10) (closed_mem 19 10) cl_11567 (by decide) v hb
def cl_11568 : CNF.NClause := [(717,true),(720,true),(723,true),(731,true),(734,true),(741,false)]
theorem inp_11568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11568 v hb
def cl_11569 : CNF.NClause := [(717,true),(720,true),(723,true),(731,true),(734,false),(741,true)]
theorem inp_11569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 11) (closed_mem 19 11) cl_11569 (by decide) v hb
def cl_11570 : CNF.NClause := [(717,true),(720,true),(723,true),(731,false),(734,true),(741,true)]
theorem inp_11570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 11) (closed_mem 19 11) cl_11570 (by decide) v hb
def cl_11571 : CNF.NClause := [(717,true),(720,true),(723,false),(731,true),(734,true),(741,true)]
theorem inp_11571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 11) (closed_mem 19 11) cl_11571 (by decide) v hb
def cl_11573 : CNF.NClause := [(717,false),(720,true),(723,true),(731,true),(734,true),(741,true)]
theorem inp_11573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 11) (closed_mem 19 11) cl_11573 (by decide) v hb
def cl_11576 : CNF.NClause := [(715,true),(719,true),(723,true),(732,false),(736,true),(742,true)]
theorem inp_11576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 12) (closed_mem 19 12) cl_11576 (by decide) v hb
def cl_11580 : CNF.NClause := [(716,true),(722,true),(723,true),(729,true),(735,true),(739,false)]
theorem inp_11580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 13) (closed_mem 19 13) cl_11580 (by decide) v hb
def cl_11581 : CNF.NClause := [(716,true),(722,true),(723,true),(729,true),(735,false),(739,true)]
theorem inp_11581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11581 v hb
def cl_11582 : CNF.NClause := [(716,true),(722,true),(723,true),(729,false),(735,true),(739,true)]
theorem inp_11582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 13) (closed_mem 19 13) cl_11582 (by decide) v hb
def cl_11583 : CNF.NClause := [(716,true),(722,true),(723,false),(729,true),(735,true),(739,true)]
theorem inp_11583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 13) (closed_mem 19 13) cl_11583 (by decide) v hb
def cl_11585 : CNF.NClause := [(716,false),(722,true),(723,true),(729,true),(735,true),(739,true)]
theorem inp_11585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 13) (closed_mem 19 13) cl_11585 (by decide) v hb
def cl_11591 : CNF.NClause := [(714,false),(721,true),(723,true),(730,true),(737,true),(740,true)]
theorem inp_11591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 14) (closed_mem 19 14) cl_11591 (by decide) v hb
def cl_11593 : CNF.NClause := [(728,true),(729,true),(730,true),(731,true),(732,false),(743,true)]
theorem inp_11593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 15) (closed_mem 19 15) cl_11593 (by decide) v hb
def cl_11600 : CNF.NClause := [(717,true),(719,true),(726,true),(728,false),(735,true),(740,true)]
theorem inp_11600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11600 v hb
def cl_11601 : CNF.NClause := [(717,true),(719,true),(726,false),(728,true),(735,true),(740,true)]
theorem inp_11601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 16) (closed_mem 19 16) cl_11601 (by decide) v hb
def cl_11603 : CNF.NClause := [(717,false),(719,true),(726,true),(728,true),(735,true),(740,true)]
theorem inp_11603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 16) (closed_mem 19 16) cl_11603 (by decide) v hb
def cl_11606 : CNF.NClause := [(715,true),(721,true),(727,true),(728,false),(734,true),(739,true)]
theorem inp_11606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 17) (closed_mem 19 17) cl_11606 (by decide) v hb
def cl_11607 : CNF.NClause := [(715,true),(721,true),(727,false),(728,true),(734,true),(739,true)]
theorem inp_11607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 17) (closed_mem 19 17) cl_11607 (by decide) v hb
def cl_11609 : CNF.NClause := [(715,false),(721,true),(727,true),(728,true),(734,true),(739,true)]
theorem inp_11609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11609 v hb
def cl_11611 : CNF.NClause := [(716,true),(720,true),(724,true),(728,true),(737,false),(742,true)]
theorem inp_11611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 18) (closed_mem 19 18) cl_11611 (by decide) v hb
def cl_11612 : CNF.NClause := [(716,true),(720,true),(724,true),(728,false),(737,true),(742,true)]
theorem inp_11612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 18) (closed_mem 19 18) cl_11612 (by decide) v hb
def cl_11613 : CNF.NClause := [(716,true),(720,true),(724,false),(728,true),(737,true),(742,true)]
theorem inp_11613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 18) (closed_mem 19 18) cl_11613 (by decide) v hb
def cl_11615 : CNF.NClause := [(716,false),(720,true),(724,true),(728,true),(737,true),(742,true)]
theorem inp_11615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 18) (closed_mem 19 18) cl_11615 (by decide) v hb
def cl_11616 : CNF.NClause := [(714,true),(722,true),(725,true),(728,true),(736,true),(741,false)]
theorem inp_11616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 19) (closed_mem 19 19) cl_11616 (by decide) v hb
def cl_11617 : CNF.NClause := [(714,true),(722,true),(725,true),(728,true),(736,false),(741,true)]
theorem inp_11617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 19) (closed_mem 19 19) cl_11617 (by decide) v hb
def cl_11619 : CNF.NClause := [(714,true),(722,true),(725,false),(728,true),(736,true),(741,true)]
theorem inp_11619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 19) (closed_mem 19 19) cl_11619 (by decide) v hb
def cl_11620 : CNF.NClause := [(714,true),(722,false),(725,true),(728,true),(736,true),(741,true)]
theorem inp_11620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 19) (closed_mem 19 19) cl_11620 (by decide) v hb
def cl_11621 : CNF.NClause := [(714,false),(722,true),(725,true),(728,true),(736,true),(741,true)]
theorem inp_11621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 19) (closed_mem 19 19) cl_11621 (by decide) v hb
def cl_11623 : CNF.NClause := [(718,true),(719,true),(720,true),(721,true),(722,false),(743,true)]
theorem inp_11623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 20) (closed_mem 19 20) cl_11623 (by decide) v hb
def cl_11624 : CNF.NClause := [(718,true),(719,true),(720,true),(721,false),(722,true),(743,true)]
theorem inp_11624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 20) (closed_mem 19 20) cl_11624 (by decide) v hb
def cl_11625 : CNF.NClause := [(718,true),(719,true),(720,false),(721,true),(722,true),(743,true)]
theorem inp_11625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11625 v hb
def cl_11626 : CNF.NClause := [(718,true),(719,false),(720,true),(721,true),(722,true),(743,true)]
theorem inp_11626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11626 v hb
def cl_11627 : CNF.NClause := [(718,false),(719,true),(720,true),(721,true),(722,true),(743,true)]
theorem inp_11627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 20) (closed_mem 19 20) cl_11627 (by decide) v hb
def cl_11629 : CNF.NClause := [(717,true),(718,true),(724,true),(730,true),(736,false),(739,true)]
theorem inp_11629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 21) (closed_mem 19 21) cl_11629 (by decide) v hb
def cl_11630 : CNF.NClause := [(717,true),(718,true),(724,true),(730,false),(736,true),(739,true)]
theorem inp_11630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 21) (closed_mem 19 21) cl_11630 (by decide) v hb
def cl_11631 : CNF.NClause := [(717,true),(718,true),(724,false),(730,true),(736,true),(739,true)]
theorem inp_11631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11631 v hb
def cl_11632 : CNF.NClause := [(717,true),(718,false),(724,true),(730,true),(736,true),(739,true)]
theorem inp_11632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 21) (closed_mem 19 21) cl_11632 (by decide) v hb
def cl_11634 : CNF.NClause := [(715,true),(718,true),(726,true),(729,true),(737,true),(741,false)]
theorem inp_11634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 22) (closed_mem 19 22) cl_11634 (by decide) v hb
def cl_11635 : CNF.NClause := [(715,true),(718,true),(726,true),(729,true),(737,false),(741,true)]
theorem inp_11635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 22) (closed_mem 19 22) cl_11635 (by decide) v hb
def cl_11636 : CNF.NClause := [(715,true),(718,true),(726,true),(729,false),(737,true),(741,true)]
theorem inp_11636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 22) (closed_mem 19 22) cl_11636 (by decide) v hb
def cl_11642 : CNF.NClause := [(716,true),(718,true),(725,true),(732,false),(734,true),(740,true)]
theorem inp_11642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11642 v hb
def cl_11646 : CNF.NClause := [(714,true),(718,true),(727,true),(731,true),(735,true),(742,false)]
theorem inp_11646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 24) (closed_mem 19 24) cl_11646 (by decide) v hb
def cl_11647 : CNF.NClause := [(714,true),(718,true),(727,true),(731,true),(735,false),(742,true)]
theorem inp_11647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 24) (closed_mem 19 24) cl_11647 (by decide) v hb
def cl_11648 : CNF.NClause := [(714,true),(718,true),(727,true),(731,false),(735,true),(742,true)]
theorem inp_11648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 24) (closed_mem 19 24) cl_11648 (by decide) v hb
def cl_11649 : CNF.NClause := [(714,true),(718,true),(727,false),(731,true),(735,true),(742,true)]
theorem inp_11649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 24) (closed_mem 19 24) cl_11649 (by decide) v hb
def cl_11651 : CNF.NClause := [(714,false),(718,true),(727,true),(731,true),(735,true),(742,true)]
theorem inp_11651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 24) (closed_mem 19 24) cl_11651 (by decide) v hb
def cl_11653 : CNF.NClause := [(713,true),(714,true),(715,true),(716,true),(717,false),(743,true)]
theorem inp_11653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 25) (closed_mem 19 25) cl_11653 (by decide) v hb
def cl_11654 : CNF.NClause := [(713,true),(714,true),(715,true),(716,false),(717,true),(743,true)]
theorem inp_11654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 25) (closed_mem 19 25) cl_11654 (by decide) v hb
def cl_11655 : CNF.NClause := [(713,true),(714,true),(715,false),(716,true),(717,true),(743,true)]
theorem inp_11655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 25) (closed_mem 19 25) cl_11655 (by decide) v hb
end Percolation.NReplay
