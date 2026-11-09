import NInputs183
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11776 : CNF.NClause := [(745,true),(752,false),(754,true),(761,true),(768,true),(771,true)]
theorem inp_11776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 14) (closed_mem 20 14) cl_11776 (by decide) v hb
def cl_11779 : CNF.NClause := [(759,true),(760,true),(761,true),(762,true),(763,false),(774,true)]
theorem inp_11779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 15) (closed_mem 20 15) cl_11779 (by decide) v hb
def cl_11780 : CNF.NClause := [(759,true),(760,true),(761,true),(762,false),(763,true),(774,true)]
theorem inp_11780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 15) (closed_mem 20 15) cl_11780 (by decide) v hb
def cl_11781 : CNF.NClause := [(759,true),(760,true),(761,false),(762,true),(763,true),(774,true)]
theorem inp_11781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 15) (closed_mem 20 15) cl_11781 (by decide) v hb
def cl_11782 : CNF.NClause := [(759,true),(760,false),(761,true),(762,true),(763,true),(774,true)]
theorem inp_11782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 15) (closed_mem 20 15) cl_11782 (by decide) v hb
def cl_11783 : CNF.NClause := [(759,false),(760,true),(761,true),(762,true),(763,true),(774,true)]
theorem inp_11783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 15) (closed_mem 20 15) cl_11783 (by decide) v hb
def cl_11784 : CNF.NClause := [(748,true),(750,true),(757,true),(759,true),(766,true),(771,false)]
theorem inp_11784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 16) (closed_mem 20 16) cl_11784 (by decide) v hb
def cl_11785 : CNF.NClause := [(748,true),(750,true),(757,true),(759,true),(766,false),(771,true)]
theorem inp_11785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 16) (closed_mem 20 16) cl_11785 (by decide) v hb
def cl_11786 : CNF.NClause := [(748,true),(750,true),(757,true),(759,false),(766,true),(771,true)]
theorem inp_11786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 16) (closed_mem 20 16) cl_11786 (by decide) v hb
def cl_11789 : CNF.NClause := [(748,false),(750,true),(757,true),(759,true),(766,true),(771,true)]
theorem inp_11789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 16) (closed_mem 20 16) cl_11789 (by decide) v hb
def cl_11791 : CNF.NClause := [(746,true),(752,true),(758,true),(759,true),(765,false),(770,true)]
theorem inp_11791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 17) (closed_mem 20 17) cl_11791 (by decide) v hb
def cl_11793 : CNF.NClause := [(746,true),(752,true),(758,false),(759,true),(765,true),(770,true)]
theorem inp_11793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 17) (closed_mem 20 17) cl_11793 (by decide) v hb
def cl_11795 : CNF.NClause := [(746,false),(752,true),(758,true),(759,true),(765,true),(770,true)]
theorem inp_11795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 17) (closed_mem 20 17) cl_11795 (by decide) v hb
def cl_11796 : CNF.NClause := [(747,true),(751,true),(755,true),(759,true),(768,true),(773,false)]
theorem inp_11796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 18) (closed_mem 20 18) cl_11796 (by decide) v hb
def cl_11799 : CNF.NClause := [(747,true),(751,true),(755,false),(759,true),(768,true),(773,true)]
theorem inp_11799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 18) (closed_mem 20 18) cl_11799 (by decide) v hb
def cl_11803 : CNF.NClause := [(745,true),(753,true),(756,true),(759,true),(767,false),(772,true)]
theorem inp_11803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 19) (closed_mem 20 19) cl_11803 (by decide) v hb
def cl_11804 : CNF.NClause := [(745,true),(753,true),(756,true),(759,false),(767,true),(772,true)]
theorem inp_11804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 19) (closed_mem 20 19) cl_11804 (by decide) v hb
def cl_11807 : CNF.NClause := [(745,false),(753,true),(756,true),(759,true),(767,true),(772,true)]
theorem inp_11807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 19) (closed_mem 20 19) cl_11807 (by decide) v hb
def cl_11809 : CNF.NClause := [(749,true),(750,true),(751,true),(752,true),(753,false),(774,true)]
theorem inp_11809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 20) (closed_mem 20 20) cl_11809 (by decide) v hb
def cl_11810 : CNF.NClause := [(749,true),(750,true),(751,true),(752,false),(753,true),(774,true)]
theorem inp_11810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 20) (closed_mem 20 20) cl_11810 (by decide) v hb
def cl_11811 : CNF.NClause := [(749,true),(750,true),(751,false),(752,true),(753,true),(774,true)]
theorem inp_11811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 20) (closed_mem 20 20) cl_11811 (by decide) v hb
def cl_11812 : CNF.NClause := [(749,true),(750,false),(751,true),(752,true),(753,true),(774,true)]
theorem inp_11812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 20) (closed_mem 20 20) cl_11812 (by decide) v hb
def cl_11813 : CNF.NClause := [(749,false),(750,true),(751,true),(752,true),(753,true),(774,true)]
theorem inp_11813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 20) (closed_mem 20 20) cl_11813 (by decide) v hb
def cl_11815 : CNF.NClause := [(748,true),(749,true),(755,true),(761,true),(767,false),(770,true)]
theorem inp_11815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 21) (closed_mem 20 21) cl_11815 (by decide) v hb
def cl_11819 : CNF.NClause := [(748,false),(749,true),(755,true),(761,true),(767,true),(770,true)]
theorem inp_11819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 21) (closed_mem 20 21) cl_11819 (by decide) v hb
def cl_11820 : CNF.NClause := [(746,true),(749,true),(757,true),(760,true),(768,true),(772,false)]
theorem inp_11820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 22) (closed_mem 20 22) cl_11820 (by decide) v hb
def cl_11824 : CNF.NClause := [(746,true),(749,false),(757,true),(760,true),(768,true),(772,true)]
theorem inp_11824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 22) (closed_mem 20 22) cl_11824 (by decide) v hb
def cl_11825 : CNF.NClause := [(746,false),(749,true),(757,true),(760,true),(768,true),(772,true)]
theorem inp_11825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 22) (closed_mem 20 22) cl_11825 (by decide) v hb
def cl_11828 : CNF.NClause := [(747,true),(749,true),(756,true),(763,false),(765,true),(771,true)]
theorem inp_11828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 23) (closed_mem 20 23) cl_11828 (by decide) v hb
def cl_11829 : CNF.NClause := [(747,true),(749,true),(756,false),(763,true),(765,true),(771,true)]
theorem inp_11829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 23) (closed_mem 20 23) cl_11829 (by decide) v hb
def cl_11830 : CNF.NClause := [(747,true),(749,false),(756,true),(763,true),(765,true),(771,true)]
theorem inp_11830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 23) (closed_mem 20 23) cl_11830 (by decide) v hb
def cl_11831 : CNF.NClause := [(747,false),(749,true),(756,true),(763,true),(765,true),(771,true)]
theorem inp_11831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 23) (closed_mem 20 23) cl_11831 (by decide) v hb
def cl_11834 : CNF.NClause := [(745,true),(749,true),(758,true),(762,false),(766,true),(773,true)]
theorem inp_11834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 24) (closed_mem 20 24) cl_11834 (by decide) v hb
def cl_11839 : CNF.NClause := [(744,true),(745,true),(746,true),(747,true),(748,false),(774,true)]
theorem inp_11839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 25) (closed_mem 20 25) cl_11839 (by decide) v hb
def cl_11840 : CNF.NClause := [(744,true),(745,true),(746,true),(747,false),(748,true),(774,true)]
theorem inp_11840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 25) (closed_mem 20 25) cl_11840 (by decide) v hb
def cl_11841 : CNF.NClause := [(744,true),(745,true),(746,false),(747,true),(748,true),(774,true)]
theorem inp_11841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 25) (closed_mem 20 25) cl_11841 (by decide) v hb
def cl_11842 : CNF.NClause := [(744,true),(745,false),(746,true),(747,true),(748,true),(774,true)]
theorem inp_11842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 25) (closed_mem 20 25) cl_11842 (by decide) v hb
def cl_11844 : CNF.NClause := [(744,true),(753,true),(757,true),(761,true),(765,true),(773,false)]
theorem inp_11844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 26) (closed_mem 20 26) cl_11844 (by decide) v hb
def cl_11845 : CNF.NClause := [(744,true),(753,true),(757,true),(761,true),(765,false),(773,true)]
theorem inp_11845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 26) (closed_mem 20 26) cl_11845 (by decide) v hb
def cl_11846 : CNF.NClause := [(744,true),(753,true),(757,true),(761,false),(765,true),(773,true)]
theorem inp_11846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 26) (closed_mem 20 26) cl_11846 (by decide) v hb
def cl_11847 : CNF.NClause := [(744,true),(753,true),(757,false),(761,true),(765,true),(773,true)]
theorem inp_11847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 26) (closed_mem 20 26) cl_11847 (by decide) v hb
def cl_11848 : CNF.NClause := [(744,true),(753,false),(757,true),(761,true),(765,true),(773,true)]
theorem inp_11848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 26) (closed_mem 20 26) cl_11848 (by decide) v hb
def cl_11851 : CNF.NClause := [(744,true),(751,true),(758,true),(760,true),(767,false),(771,true)]
theorem inp_11851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 27) (closed_mem 20 27) cl_11851 (by decide) v hb
def cl_11852 : CNF.NClause := [(744,true),(751,true),(758,true),(760,false),(767,true),(771,true)]
theorem inp_11852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 27) (closed_mem 20 27) cl_11852 (by decide) v hb
def cl_11853 : CNF.NClause := [(744,true),(751,true),(758,false),(760,true),(767,true),(771,true)]
theorem inp_11853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 27) (closed_mem 20 27) cl_11853 (by decide) v hb
def cl_11856 : CNF.NClause := [(744,true),(752,true),(755,true),(763,true),(766,true),(772,false)]
theorem inp_11856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 28) (closed_mem 20 28) cl_11856 (by decide) v hb
def cl_11858 : CNF.NClause := [(744,true),(752,true),(755,true),(763,false),(766,true),(772,true)]
theorem inp_11858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 28) (closed_mem 20 28) cl_11858 (by decide) v hb
def cl_11859 : CNF.NClause := [(744,true),(752,true),(755,false),(763,true),(766,true),(772,true)]
theorem inp_11859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 28) (closed_mem 20 28) cl_11859 (by decide) v hb
def cl_11860 : CNF.NClause := [(744,true),(752,false),(755,true),(763,true),(766,true),(772,true)]
theorem inp_11860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 28) (closed_mem 20 28) cl_11860 (by decide) v hb
def cl_11862 : CNF.NClause := [(744,true),(750,true),(756,true),(762,true),(768,true),(770,false)]
theorem inp_11862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 29) (closed_mem 20 29) cl_11862 (by decide) v hb
end Percolation.NReplay
