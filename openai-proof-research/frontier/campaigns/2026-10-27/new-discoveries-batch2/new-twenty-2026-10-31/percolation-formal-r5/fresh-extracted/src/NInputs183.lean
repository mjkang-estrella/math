import NInputs182
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11656 : CNF.NClause := [(713,true),(714,false),(715,true),(716,true),(717,true),(743,true)]
theorem inp_11656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11656 v hb
def cl_11658 : CNF.NClause := [(713,true),(722,true),(726,true),(730,true),(734,true),(742,false)]
theorem inp_11658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 26) (closed_mem 19 26) cl_11658 (by decide) v hb
def cl_11659 : CNF.NClause := [(713,true),(722,true),(726,true),(730,true),(734,false),(742,true)]
theorem inp_11659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 26) (closed_mem 19 26) cl_11659 (by decide) v hb
def cl_11660 : CNF.NClause := [(713,true),(722,true),(726,true),(730,false),(734,true),(742,true)]
theorem inp_11660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 26) (closed_mem 19 26) cl_11660 (by decide) v hb
def cl_11661 : CNF.NClause := [(713,true),(722,true),(726,false),(730,true),(734,true),(742,true)]
theorem inp_11661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 26) (closed_mem 19 26) cl_11661 (by decide) v hb
def cl_11662 : CNF.NClause := [(713,true),(722,false),(726,true),(730,true),(734,true),(742,true)]
theorem inp_11662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11662 v hb
def cl_11664 : CNF.NClause := [(713,true),(720,true),(727,true),(729,true),(736,true),(740,false)]
theorem inp_11664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 27) (closed_mem 19 27) cl_11664 (by decide) v hb
def cl_11665 : CNF.NClause := [(713,true),(720,true),(727,true),(729,true),(736,false),(740,true)]
theorem inp_11665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 27) (closed_mem 19 27) cl_11665 (by decide) v hb
def cl_11667 : CNF.NClause := [(713,true),(720,true),(727,false),(729,true),(736,true),(740,true)]
theorem inp_11667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 27) (closed_mem 19 27) cl_11667 (by decide) v hb
def cl_11668 : CNF.NClause := [(713,true),(720,false),(727,true),(729,true),(736,true),(740,true)]
theorem inp_11668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 27) (closed_mem 19 27) cl_11668 (by decide) v hb
def cl_11672 : CNF.NClause := [(713,true),(721,true),(724,true),(732,false),(735,true),(741,true)]
theorem inp_11672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 28) (closed_mem 19 28) cl_11672 (by decide) v hb
def cl_11676 : CNF.NClause := [(713,true),(719,true),(725,true),(731,true),(737,true),(739,false)]
theorem inp_11676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 29) (closed_mem 19 29) cl_11676 (by decide) v hb
def cl_11677 : CNF.NClause := [(713,true),(719,true),(725,true),(731,true),(737,false),(739,true)]
theorem inp_11677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 29) (closed_mem 19 29) cl_11677 (by decide) v hb
def cl_11678 : CNF.NClause := [(713,true),(719,true),(725,true),(731,false),(737,true),(739,true)]
theorem inp_11678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 29) (closed_mem 19 29) cl_11678 (by decide) v hb
def cl_11679 : CNF.NClause := [(713,true),(719,true),(725,false),(731,true),(737,true),(739,true)]
theorem inp_11679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 29) (closed_mem 19 29) cl_11679 (by decide) v hb
def cl_11680 : CNF.NClause := [(713,true),(719,false),(725,true),(731,true),(737,true),(739,true)]
theorem inp_11680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 29) (closed_mem 19 29) cl_11680 (by decide) v hb
def cl_11683 : CNF.NClause := [(713,true),(718,true),(723,true),(728,true),(733,false),(738,true)]
theorem inp_11683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 30) (closed_mem 19 30) cl_11683 (by decide) v hb
def cl_11684 : CNF.NClause := [(713,true),(718,true),(723,true),(728,false),(733,true),(738,true)]
theorem inp_11684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 30) (closed_mem 19 30) cl_11684 (by decide) v hb
def cl_11685 : CNF.NClause := [(713,true),(718,true),(723,false),(728,true),(733,true),(738,true)]
theorem inp_11685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 30) (closed_mem 19 30) cl_11685 (by decide) v hb
def cl_11686 : CNF.NClause := [(713,true),(718,false),(723,true),(728,true),(733,true),(738,true)]
theorem inp_11686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 19 30) (closed_mem 19 30) cl_11686 (by decide) v hb
def cl_11689 : CNF.NClause := [(769,true),(770,true),(771,true),(772,true),(773,false),(774,true)]
theorem inp_11689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 0) (closed_mem 20 0) cl_11689 (by decide) v hb
def cl_11690 : CNF.NClause := [(769,true),(770,true),(771,true),(772,false),(773,true),(774,true)]
theorem inp_11690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 0) (closed_mem 20 0) cl_11690 (by decide) v hb
def cl_11691 : CNF.NClause := [(769,true),(770,true),(771,false),(772,true),(773,true),(774,true)]
theorem inp_11691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 0) (closed_mem 20 0) cl_11691 (by decide) v hb
def cl_11692 : CNF.NClause := [(769,true),(770,false),(771,true),(772,true),(773,true),(774,true)]
theorem inp_11692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 0) (closed_mem 20 0) cl_11692 (by decide) v hb
def cl_11695 : CNF.NClause := [(748,true),(753,true),(758,true),(763,true),(768,false),(769,true)]
theorem inp_11695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 1) (closed_mem 20 1) cl_11695 (by decide) v hb
def cl_11697 : CNF.NClause := [(748,true),(753,true),(758,false),(763,true),(768,true),(769,true)]
theorem inp_11697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 1) (closed_mem 20 1) cl_11697 (by decide) v hb
def cl_11699 : CNF.NClause := [(748,false),(753,true),(758,true),(763,true),(768,true),(769,true)]
theorem inp_11699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 1) (closed_mem 20 1) cl_11699 (by decide) v hb
def cl_11701 : CNF.NClause := [(746,true),(751,true),(756,true),(761,true),(766,false),(769,true)]
theorem inp_11701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 2) (closed_mem 20 2) cl_11701 (by decide) v hb
def cl_11703 : CNF.NClause := [(746,true),(751,true),(756,false),(761,true),(766,true),(769,true)]
theorem inp_11703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 2) (closed_mem 20 2) cl_11703 (by decide) v hb
def cl_11705 : CNF.NClause := [(746,false),(751,true),(756,true),(761,true),(766,true),(769,true)]
theorem inp_11705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 2) (closed_mem 20 2) cl_11705 (by decide) v hb
def cl_11707 : CNF.NClause := [(747,true),(752,true),(757,true),(762,true),(767,false),(769,true)]
theorem inp_11707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 3) (closed_mem 20 3) cl_11707 (by decide) v hb
def cl_11709 : CNF.NClause := [(747,true),(752,true),(757,false),(762,true),(767,true),(769,true)]
theorem inp_11709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 3) (closed_mem 20 3) cl_11709 (by decide) v hb
def cl_11710 : CNF.NClause := [(747,true),(752,false),(757,true),(762,true),(767,true),(769,true)]
theorem inp_11710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 3) (closed_mem 20 3) cl_11710 (by decide) v hb
def cl_11713 : CNF.NClause := [(745,true),(750,true),(755,true),(760,true),(765,false),(769,true)]
theorem inp_11713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 4) (closed_mem 20 4) cl_11713 (by decide) v hb
def cl_11716 : CNF.NClause := [(745,true),(750,false),(755,true),(760,true),(765,true),(769,true)]
theorem inp_11716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 4) (closed_mem 20 4) cl_11716 (by decide) v hb
def cl_11717 : CNF.NClause := [(745,false),(750,true),(755,true),(760,true),(765,true),(769,true)]
theorem inp_11717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 4) (closed_mem 20 4) cl_11717 (by decide) v hb
def cl_11723 : CNF.NClause := [(764,false),(765,true),(766,true),(767,true),(768,true),(774,true)]
theorem inp_11723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 5) (closed_mem 20 5) cl_11723 (by decide) v hb
def cl_11725 : CNF.NClause := [(748,true),(752,true),(756,true),(760,true),(764,false),(773,true)]
theorem inp_11725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 6) (closed_mem 20 6) cl_11725 (by decide) v hb
def cl_11731 : CNF.NClause := [(746,true),(753,true),(755,true),(762,true),(764,false),(771,true)]
theorem inp_11731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 7) (closed_mem 20 7) cl_11731 (by decide) v hb
def cl_11737 : CNF.NClause := [(747,true),(750,true),(758,true),(761,true),(764,false),(772,true)]
theorem inp_11737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 8) (closed_mem 20 8) cl_11737 (by decide) v hb
def cl_11743 : CNF.NClause := [(745,true),(751,true),(757,true),(763,true),(764,false),(770,true)]
theorem inp_11743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 9) (closed_mem 20 9) cl_11743 (by decide) v hb
def cl_11750 : CNF.NClause := [(754,true),(755,true),(756,true),(757,false),(758,true),(774,true)]
theorem inp_11750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 10) (closed_mem 20 10) cl_11750 (by decide) v hb
def cl_11753 : CNF.NClause := [(754,false),(755,true),(756,true),(757,true),(758,true),(774,true)]
theorem inp_11753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 10) (closed_mem 20 10) cl_11753 (by decide) v hb
def cl_11755 : CNF.NClause := [(748,true),(751,true),(754,true),(762,true),(765,false),(772,true)]
theorem inp_11755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 11) (closed_mem 20 11) cl_11755 (by decide) v hb
def cl_11757 : CNF.NClause := [(748,true),(751,true),(754,false),(762,true),(765,true),(772,true)]
theorem inp_11757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 11) (closed_mem 20 11) cl_11757 (by decide) v hb
def cl_11760 : CNF.NClause := [(746,true),(750,true),(754,true),(763,true),(767,true),(773,false)]
theorem inp_11760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 12) (closed_mem 20 12) cl_11760 (by decide) v hb
def cl_11761 : CNF.NClause := [(746,true),(750,true),(754,true),(763,true),(767,false),(773,true)]
theorem inp_11761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 12) (closed_mem 20 12) cl_11761 (by decide) v hb
def cl_11767 : CNF.NClause := [(747,true),(753,true),(754,true),(760,true),(766,false),(770,true)]
theorem inp_11767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 13) (closed_mem 20 13) cl_11767 (by decide) v hb
def cl_11769 : CNF.NClause := [(747,true),(753,true),(754,false),(760,true),(766,true),(770,true)]
theorem inp_11769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 13) (closed_mem 20 13) cl_11769 (by decide) v hb
def cl_11770 : CNF.NClause := [(747,true),(753,false),(754,true),(760,true),(766,true),(770,true)]
theorem inp_11770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 13) (closed_mem 20 13) cl_11770 (by decide) v hb
end Percolation.NReplay
