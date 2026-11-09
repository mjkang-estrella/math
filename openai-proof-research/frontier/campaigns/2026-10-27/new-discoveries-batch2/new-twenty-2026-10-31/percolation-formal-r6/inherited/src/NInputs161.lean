import NInputs160
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9734 : CNF.NClause := [(418,true),(419,true),(420,true),(421,false),(422,true),(433,true)]
theorem inp_9734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) cl_9734 (by decide) v hb
def cl_9735 : CNF.NClause := [(418,true),(419,true),(420,false),(421,true),(422,true),(433,true)]
theorem inp_9735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) cl_9735 (by decide) v hb
def cl_9736 : CNF.NClause := [(418,true),(419,false),(420,true),(421,true),(422,true),(433,true)]
theorem inp_9736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) cl_9736 (by decide) v hb
def cl_9737 : CNF.NClause := [(418,false),(419,true),(420,true),(421,true),(422,true),(433,true)]
theorem inp_9737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) cl_9737 (by decide) v hb
def cl_9740 : CNF.NClause := [(407,true),(409,true),(416,true),(418,false),(425,true),(430,true)]
theorem inp_9740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 16) (closed_mem 9 16) cl_9740 (by decide) v hb
def cl_9742 : CNF.NClause := [(407,true),(409,false),(416,true),(418,true),(425,true),(430,true)]
theorem inp_9742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 16) (closed_mem 9 16) cl_9742 (by decide) v hb
def cl_9743 : CNF.NClause := [(407,false),(409,true),(416,true),(418,true),(425,true),(430,true)]
theorem inp_9743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 16) (closed_mem 9 16) cl_9743 (by decide) v hb
def cl_9744 : CNF.NClause := [(405,true),(411,true),(417,true),(418,true),(424,true),(429,false)]
theorem inp_9744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) cl_9744 (by decide) v hb
def cl_9746 : CNF.NClause := [(405,true),(411,true),(417,true),(418,false),(424,true),(429,true)]
theorem inp_9746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) cl_9746 (by decide) v hb
def cl_9747 : CNF.NClause := [(405,true),(411,true),(417,false),(418,true),(424,true),(429,true)]
theorem inp_9747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) cl_9747 (by decide) v hb
def cl_9748 : CNF.NClause := [(405,true),(411,false),(417,true),(418,true),(424,true),(429,true)]
theorem inp_9748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) cl_9748 (by decide) v hb
def cl_9750 : CNF.NClause := [(406,true),(410,true),(414,true),(418,true),(427,true),(432,false)]
theorem inp_9750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) cl_9750 (by decide) v hb
def cl_9751 : CNF.NClause := [(406,true),(410,true),(414,true),(418,true),(427,false),(432,true)]
theorem inp_9751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) cl_9751 (by decide) v hb
def cl_9752 : CNF.NClause := [(406,true),(410,true),(414,true),(418,false),(427,true),(432,true)]
theorem inp_9752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) cl_9752 (by decide) v hb
def cl_9753 : CNF.NClause := [(406,true),(410,true),(414,false),(418,true),(427,true),(432,true)]
theorem inp_9753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) cl_9753 (by decide) v hb
def cl_9754 : CNF.NClause := [(406,true),(410,false),(414,true),(418,true),(427,true),(432,true)]
theorem inp_9754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) cl_9754 (by decide) v hb
def cl_9755 : CNF.NClause := [(406,false),(410,true),(414,true),(418,true),(427,true),(432,true)]
theorem inp_9755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) cl_9755 (by decide) v hb
def cl_9760 : CNF.NClause := [(404,true),(412,false),(415,true),(418,true),(426,true),(431,true)]
theorem inp_9760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 19) (closed_mem 9 19) cl_9760 (by decide) v hb
def cl_9763 : CNF.NClause := [(408,true),(409,true),(410,true),(411,true),(412,false),(433,true)]
theorem inp_9763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 20) (closed_mem 9 20) cl_9763 (by decide) v hb
def cl_9769 : CNF.NClause := [(407,true),(408,true),(414,true),(420,true),(426,false),(429,true)]
theorem inp_9769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) cl_9769 (by decide) v hb
def cl_9770 : CNF.NClause := [(407,true),(408,true),(414,true),(420,false),(426,true),(429,true)]
theorem inp_9770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) cl_9770 (by decide) v hb
def cl_9771 : CNF.NClause := [(407,true),(408,true),(414,false),(420,true),(426,true),(429,true)]
theorem inp_9771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) cl_9771 (by decide) v hb
def cl_9772 : CNF.NClause := [(407,true),(408,false),(414,true),(420,true),(426,true),(429,true)]
theorem inp_9772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) cl_9772 (by decide) v hb
def cl_9773 : CNF.NClause := [(407,false),(408,true),(414,true),(420,true),(426,true),(429,true)]
theorem inp_9773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) cl_9773 (by decide) v hb
def cl_9774 : CNF.NClause := [(405,true),(408,true),(416,true),(419,true),(427,true),(431,false)]
theorem inp_9774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) cl_9774 (by decide) v hb
def cl_9775 : CNF.NClause := [(405,true),(408,true),(416,true),(419,true),(427,false),(431,true)]
theorem inp_9775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) cl_9775 (by decide) v hb
def cl_9776 : CNF.NClause := [(405,true),(408,true),(416,true),(419,false),(427,true),(431,true)]
theorem inp_9776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) cl_9776 (by decide) v hb
def cl_9777 : CNF.NClause := [(405,true),(408,true),(416,false),(419,true),(427,true),(431,true)]
theorem inp_9777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) cl_9777 (by decide) v hb
def cl_9778 : CNF.NClause := [(405,true),(408,false),(416,true),(419,true),(427,true),(431,true)]
theorem inp_9778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) cl_9778 (by decide) v hb
def cl_9779 : CNF.NClause := [(405,false),(408,true),(416,true),(419,true),(427,true),(431,true)]
theorem inp_9779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) cl_9779 (by decide) v hb
def cl_9780 : CNF.NClause := [(406,true),(408,true),(415,true),(422,true),(424,true),(430,false)]
theorem inp_9780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 23) (closed_mem 9 23) cl_9780 (by decide) v hb
def cl_9783 : CNF.NClause := [(406,true),(408,true),(415,false),(422,true),(424,true),(430,true)]
theorem inp_9783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 23) (closed_mem 9 23) cl_9783 (by decide) v hb
def cl_9784 : CNF.NClause := [(406,true),(408,false),(415,true),(422,true),(424,true),(430,true)]
theorem inp_9784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 23) (closed_mem 9 23) cl_9784 (by decide) v hb
def cl_9785 : CNF.NClause := [(406,false),(408,true),(415,true),(422,true),(424,true),(430,true)]
theorem inp_9785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 23) (closed_mem 9 23) cl_9785 (by decide) v hb
def cl_9786 : CNF.NClause := [(404,true),(408,true),(417,true),(421,true),(425,true),(432,false)]
theorem inp_9786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) cl_9786 (by decide) v hb
def cl_9787 : CNF.NClause := [(404,true),(408,true),(417,true),(421,true),(425,false),(432,true)]
theorem inp_9787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) cl_9787 (by decide) v hb
def cl_9788 : CNF.NClause := [(404,true),(408,true),(417,true),(421,false),(425,true),(432,true)]
theorem inp_9788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) cl_9788 (by decide) v hb
def cl_9790 : CNF.NClause := [(404,true),(408,false),(417,true),(421,true),(425,true),(432,true)]
theorem inp_9790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) cl_9790 (by decide) v hb
def cl_9791 : CNF.NClause := [(404,false),(408,true),(417,true),(421,true),(425,true),(432,true)]
theorem inp_9791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) cl_9791 (by decide) v hb
def cl_9793 : CNF.NClause := [(403,true),(404,true),(405,true),(406,true),(407,false),(433,true)]
theorem inp_9793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 25) (closed_mem 9 25) cl_9793 (by decide) v hb
def cl_9794 : CNF.NClause := [(403,true),(404,true),(405,true),(406,false),(407,true),(433,true)]
theorem inp_9794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 25) (closed_mem 9 25) cl_9794 (by decide) v hb
def cl_9795 : CNF.NClause := [(403,true),(404,true),(405,false),(406,true),(407,true),(433,true)]
theorem inp_9795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 25) (closed_mem 9 25) cl_9795 (by decide) v hb
def cl_9796 : CNF.NClause := [(403,true),(404,false),(405,true),(406,true),(407,true),(433,true)]
theorem inp_9796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 25) (closed_mem 9 25) cl_9796 (by decide) v hb
def cl_9802 : CNF.NClause := [(403,true),(412,false),(416,true),(420,true),(424,true),(432,true)]
theorem inp_9802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 26) (closed_mem 9 26) cl_9802 (by decide) v hb
def cl_9804 : CNF.NClause := [(403,true),(410,true),(417,true),(419,true),(426,true),(430,false)]
theorem inp_9804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) cl_9804 (by decide) v hb
def cl_9805 : CNF.NClause := [(403,true),(410,true),(417,true),(419,true),(426,false),(430,true)]
theorem inp_9805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) cl_9805 (by decide) v hb
def cl_9806 : CNF.NClause := [(403,true),(410,true),(417,true),(419,false),(426,true),(430,true)]
theorem inp_9806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) cl_9806 (by decide) v hb
def cl_9807 : CNF.NClause := [(403,true),(410,true),(417,false),(419,true),(426,true),(430,true)]
theorem inp_9807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) cl_9807 (by decide) v hb
def cl_9808 : CNF.NClause := [(403,true),(410,false),(417,true),(419,true),(426,true),(430,true)]
theorem inp_9808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) cl_9808 (by decide) v hb
def cl_9810 : CNF.NClause := [(403,true),(411,true),(414,true),(422,true),(425,true),(431,false)]
theorem inp_9810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) cl_9810 (by decide) v hb
end Percolation.NReplay
