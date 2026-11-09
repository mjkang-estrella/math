import NInputs172
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10749 : CNF.NClause := [(558,true),(564,true),(570,false),(576,true),(582,true),(584,true)]
theorem inp_10749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 29) (closed_mem 14 29) cl_10749 (by decide) v hb
def cl_10750 : CNF.NClause := [(558,true),(564,false),(570,true),(576,true),(582,true),(584,true)]
theorem inp_10750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 29) (closed_mem 14 29) cl_10750 (by decide) v hb
def cl_10753 : CNF.NClause := [(558,true),(563,true),(568,true),(573,true),(578,false),(583,true)]
theorem inp_10753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 30) (closed_mem 14 30) cl_10753 (by decide) v hb
def cl_10754 : CNF.NClause := [(558,true),(563,true),(568,true),(573,false),(578,true),(583,true)]
theorem inp_10754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 30) (closed_mem 14 30) cl_10754 (by decide) v hb
def cl_10755 : CNF.NClause := [(558,true),(563,true),(568,false),(573,true),(578,true),(583,true)]
theorem inp_10755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 30) (closed_mem 14 30) cl_10755 (by decide) v hb
def cl_10756 : CNF.NClause := [(558,true),(563,false),(568,true),(573,true),(578,true),(583,true)]
theorem inp_10756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 30) (closed_mem 14 30) cl_10756 (by decide) v hb
def cl_10759 : CNF.NClause := [(614,true),(615,true),(616,true),(617,true),(618,false),(619,true)]
theorem inp_10759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 0) (closed_mem 15 0) cl_10759 (by decide) v hb
def cl_10761 : CNF.NClause := [(614,true),(615,true),(616,false),(617,true),(618,true),(619,true)]
theorem inp_10761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 0) (closed_mem 15 0) cl_10761 (by decide) v hb
def cl_10768 : CNF.NClause := [(593,true),(598,false),(603,true),(608,true),(613,true),(614,true)]
theorem inp_10768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 1) (closed_mem 15 1) cl_10768 (by decide) v hb
def cl_10769 : CNF.NClause := [(593,false),(598,true),(603,true),(608,true),(613,true),(614,true)]
theorem inp_10769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 1) (closed_mem 15 1) cl_10769 (by decide) v hb
def cl_10771 : CNF.NClause := [(591,true),(596,true),(601,true),(606,true),(611,false),(614,true)]
theorem inp_10771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 2) (closed_mem 15 2) cl_10771 (by decide) v hb
def cl_10772 : CNF.NClause := [(591,true),(596,true),(601,true),(606,false),(611,true),(614,true)]
theorem inp_10772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 2) (closed_mem 15 2) cl_10772 (by decide) v hb
def cl_10773 : CNF.NClause := [(591,true),(596,true),(601,false),(606,true),(611,true),(614,true)]
theorem inp_10773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 2) (closed_mem 15 2) cl_10773 (by decide) v hb
def cl_10775 : CNF.NClause := [(591,false),(596,true),(601,true),(606,true),(611,true),(614,true)]
theorem inp_10775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 2) (closed_mem 15 2) cl_10775 (by decide) v hb
def cl_10777 : CNF.NClause := [(592,true),(597,true),(602,true),(607,true),(612,false),(614,true)]
theorem inp_10777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 3) (closed_mem 15 3) cl_10777 (by decide) v hb
def cl_10779 : CNF.NClause := [(592,true),(597,true),(602,false),(607,true),(612,true),(614,true)]
theorem inp_10779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 3) (closed_mem 15 3) cl_10779 (by decide) v hb
def cl_10780 : CNF.NClause := [(592,true),(597,false),(602,true),(607,true),(612,true),(614,true)]
theorem inp_10780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 3) (closed_mem 15 3) cl_10780 (by decide) v hb
def cl_10781 : CNF.NClause := [(592,false),(597,true),(602,true),(607,true),(612,true),(614,true)]
theorem inp_10781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 3) (closed_mem 15 3) cl_10781 (by decide) v hb
def cl_10783 : CNF.NClause := [(590,true),(595,true),(600,true),(605,true),(610,false),(614,true)]
theorem inp_10783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 4) (closed_mem 15 4) cl_10783 (by decide) v hb
def cl_10784 : CNF.NClause := [(590,true),(595,true),(600,true),(605,false),(610,true),(614,true)]
theorem inp_10784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 4) (closed_mem 15 4) cl_10784 (by decide) v hb
def cl_10785 : CNF.NClause := [(590,true),(595,true),(600,false),(605,true),(610,true),(614,true)]
theorem inp_10785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 4) (closed_mem 15 4) cl_10785 (by decide) v hb
def cl_10789 : CNF.NClause := [(609,true),(610,true),(611,true),(612,true),(613,false),(619,true)]
theorem inp_10789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 5) (closed_mem 15 5) cl_10789 (by decide) v hb
def cl_10790 : CNF.NClause := [(609,true),(610,true),(611,true),(612,false),(613,true),(619,true)]
theorem inp_10790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 5) (closed_mem 15 5) cl_10790 (by decide) v hb
def cl_10791 : CNF.NClause := [(609,true),(610,true),(611,false),(612,true),(613,true),(619,true)]
theorem inp_10791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 5) (closed_mem 15 5) cl_10791 (by decide) v hb
def cl_10793 : CNF.NClause := [(609,false),(610,true),(611,true),(612,true),(613,true),(619,true)]
theorem inp_10793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 5) (closed_mem 15 5) cl_10793 (by decide) v hb
def cl_10797 : CNF.NClause := [(593,true),(597,true),(601,false),(605,true),(609,true),(618,true)]
theorem inp_10797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 6) (closed_mem 15 6) cl_10797 (by decide) v hb
def cl_10798 : CNF.NClause := [(593,true),(597,false),(601,true),(605,true),(609,true),(618,true)]
theorem inp_10798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 6) (closed_mem 15 6) cl_10798 (by decide) v hb
def cl_10799 : CNF.NClause := [(593,false),(597,true),(601,true),(605,true),(609,true),(618,true)]
theorem inp_10799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 6) (closed_mem 15 6) cl_10799 (by decide) v hb
def cl_10800 : CNF.NClause := [(591,true),(598,true),(600,true),(607,true),(609,true),(616,false)]
theorem inp_10800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 7) (closed_mem 15 7) cl_10800 (by decide) v hb
def cl_10801 : CNF.NClause := [(591,true),(598,true),(600,true),(607,true),(609,false),(616,true)]
theorem inp_10801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 7) (closed_mem 15 7) cl_10801 (by decide) v hb
def cl_10803 : CNF.NClause := [(591,true),(598,true),(600,false),(607,true),(609,true),(616,true)]
theorem inp_10803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 7) (closed_mem 15 7) cl_10803 (by decide) v hb
def cl_10804 : CNF.NClause := [(591,true),(598,false),(600,true),(607,true),(609,true),(616,true)]
theorem inp_10804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 7) (closed_mem 15 7) cl_10804 (by decide) v hb
def cl_10805 : CNF.NClause := [(591,false),(598,true),(600,true),(607,true),(609,true),(616,true)]
theorem inp_10805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 7) (closed_mem 15 7) cl_10805 (by decide) v hb
def cl_10806 : CNF.NClause := [(592,true),(595,true),(603,true),(606,true),(609,true),(617,false)]
theorem inp_10806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 8) (closed_mem 15 8) cl_10806 (by decide) v hb
def cl_10809 : CNF.NClause := [(592,true),(595,true),(603,false),(606,true),(609,true),(617,true)]
theorem inp_10809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 8) (closed_mem 15 8) cl_10809 (by decide) v hb
def cl_10810 : CNF.NClause := [(592,true),(595,false),(603,true),(606,true),(609,true),(617,true)]
theorem inp_10810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 8) (closed_mem 15 8) cl_10810 (by decide) v hb
def cl_10811 : CNF.NClause := [(592,false),(595,true),(603,true),(606,true),(609,true),(617,true)]
theorem inp_10811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 8) (closed_mem 15 8) cl_10811 (by decide) v hb
def cl_10813 : CNF.NClause := [(590,true),(596,true),(602,true),(608,true),(609,false),(615,true)]
theorem inp_10813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 9) (closed_mem 15 9) cl_10813 (by decide) v hb
def cl_10817 : CNF.NClause := [(590,false),(596,true),(602,true),(608,true),(609,true),(615,true)]
theorem inp_10817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 9) (closed_mem 15 9) cl_10817 (by decide) v hb
def cl_10819 : CNF.NClause := [(599,true),(600,true),(601,true),(602,true),(603,false),(619,true)]
theorem inp_10819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 10) (closed_mem 15 10) cl_10819 (by decide) v hb
def cl_10822 : CNF.NClause := [(599,true),(600,false),(601,true),(602,true),(603,true),(619,true)]
theorem inp_10822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 10) (closed_mem 15 10) cl_10822 (by decide) v hb
def cl_10823 : CNF.NClause := [(599,false),(600,true),(601,true),(602,true),(603,true),(619,true)]
theorem inp_10823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 10) (closed_mem 15 10) cl_10823 (by decide) v hb
def cl_10825 : CNF.NClause := [(593,true),(596,true),(599,true),(607,true),(610,false),(617,true)]
theorem inp_10825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 11) (closed_mem 15 11) cl_10825 (by decide) v hb
def cl_10826 : CNF.NClause := [(593,true),(596,true),(599,true),(607,false),(610,true),(617,true)]
theorem inp_10826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 11) (closed_mem 15 11) cl_10826 (by decide) v hb
def cl_10828 : CNF.NClause := [(593,true),(596,false),(599,true),(607,true),(610,true),(617,true)]
theorem inp_10828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 11) (closed_mem 15 11) cl_10828 (by decide) v hb
def cl_10832 : CNF.NClause := [(591,true),(595,true),(599,true),(608,false),(612,true),(618,true)]
theorem inp_10832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 12) (closed_mem 15 12) cl_10832 (by decide) v hb
def cl_10833 : CNF.NClause := [(591,true),(595,true),(599,false),(608,true),(612,true),(618,true)]
theorem inp_10833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 12) (closed_mem 15 12) cl_10833 (by decide) v hb
def cl_10837 : CNF.NClause := [(592,true),(598,true),(599,true),(605,true),(611,false),(615,true)]
theorem inp_10837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 13) (closed_mem 15 13) cl_10837 (by decide) v hb
def cl_10839 : CNF.NClause := [(592,true),(598,true),(599,false),(605,true),(611,true),(615,true)]
theorem inp_10839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 13) (closed_mem 15 13) cl_10839 (by decide) v hb
def cl_10841 : CNF.NClause := [(592,false),(598,true),(599,true),(605,true),(611,true),(615,true)]
theorem inp_10841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 13) (closed_mem 15 13) cl_10841 (by decide) v hb
end Percolation.NReplay
