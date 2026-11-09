import NInputs159
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9658 : CNF.NClause := [(405,true),(410,false),(415,true),(420,true),(425,true),(428,true)]
theorem inp_9658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) cl_9658 (by decide) v hb
def cl_9659 : CNF.NClause := [(405,false),(410,true),(415,true),(420,true),(425,true),(428,true)]
theorem inp_9659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) cl_9659 (by decide) v hb
def cl_9661 : CNF.NClause := [(406,true),(411,true),(416,true),(421,true),(426,false),(428,true)]
theorem inp_9661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 3) (closed_mem 9 3) cl_9661 (by decide) v hb
def cl_9664 : CNF.NClause := [(406,true),(411,false),(416,true),(421,true),(426,true),(428,true)]
theorem inp_9664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 3) (closed_mem 9 3) cl_9664 (by decide) v hb
def cl_9665 : CNF.NClause := [(406,false),(411,true),(416,true),(421,true),(426,true),(428,true)]
theorem inp_9665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 3) (closed_mem 9 3) cl_9665 (by decide) v hb
def cl_9667 : CNF.NClause := [(404,true),(409,true),(414,true),(419,true),(424,false),(428,true)]
theorem inp_9667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) cl_9667 (by decide) v hb
def cl_9668 : CNF.NClause := [(404,true),(409,true),(414,true),(419,false),(424,true),(428,true)]
theorem inp_9668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) cl_9668 (by decide) v hb
def cl_9669 : CNF.NClause := [(404,true),(409,true),(414,false),(419,true),(424,true),(428,true)]
theorem inp_9669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) cl_9669 (by decide) v hb
def cl_9670 : CNF.NClause := [(404,true),(409,false),(414,true),(419,true),(424,true),(428,true)]
theorem inp_9670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) cl_9670 (by decide) v hb
def cl_9671 : CNF.NClause := [(404,false),(409,true),(414,true),(419,true),(424,true),(428,true)]
theorem inp_9671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) cl_9671 (by decide) v hb
def cl_9673 : CNF.NClause := [(423,true),(424,true),(425,true),(426,true),(427,false),(433,true)]
theorem inp_9673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) cl_9673 (by decide) v hb
def cl_9674 : CNF.NClause := [(423,true),(424,true),(425,true),(426,false),(427,true),(433,true)]
theorem inp_9674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) cl_9674 (by decide) v hb
def cl_9675 : CNF.NClause := [(423,true),(424,true),(425,false),(426,true),(427,true),(433,true)]
theorem inp_9675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9675 v hb
def cl_9676 : CNF.NClause := [(423,true),(424,false),(425,true),(426,true),(427,true),(433,true)]
theorem inp_9676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) cl_9676 (by decide) v hb
def cl_9677 : CNF.NClause := [(423,false),(424,true),(425,true),(426,true),(427,true),(433,true)]
theorem inp_9677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) cl_9677 (by decide) v hb
def cl_9680 : CNF.NClause := [(407,true),(411,true),(415,true),(419,false),(423,true),(432,true)]
theorem inp_9680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) cl_9680 (by decide) v hb
def cl_9681 : CNF.NClause := [(407,true),(411,true),(415,false),(419,true),(423,true),(432,true)]
theorem inp_9681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) cl_9681 (by decide) v hb
def cl_9682 : CNF.NClause := [(407,true),(411,false),(415,true),(419,true),(423,true),(432,true)]
theorem inp_9682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) cl_9682 (by decide) v hb
def cl_9683 : CNF.NClause := [(407,false),(411,true),(415,true),(419,true),(423,true),(432,true)]
theorem inp_9683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9683 v hb
def cl_9688 : CNF.NClause := [(405,true),(412,false),(414,true),(421,true),(423,true),(430,true)]
theorem inp_9688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 7) (closed_mem 9 7) cl_9688 (by decide) v hb
def cl_9690 : CNF.NClause := [(406,true),(409,true),(417,true),(420,true),(423,true),(431,false)]
theorem inp_9690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) cl_9690 (by decide) v hb
def cl_9691 : CNF.NClause := [(406,true),(409,true),(417,true),(420,true),(423,false),(431,true)]
theorem inp_9691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) cl_9691 (by decide) v hb
def cl_9693 : CNF.NClause := [(406,true),(409,true),(417,false),(420,true),(423,true),(431,true)]
theorem inp_9693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) cl_9693 (by decide) v hb
def cl_9694 : CNF.NClause := [(406,true),(409,false),(417,true),(420,true),(423,true),(431,true)]
theorem inp_9694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9694 v hb
def cl_9695 : CNF.NClause := [(406,false),(409,true),(417,true),(420,true),(423,true),(431,true)]
theorem inp_9695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) cl_9695 (by decide) v hb
def cl_9697 : CNF.NClause := [(404,true),(410,true),(416,true),(422,true),(423,false),(429,true)]
theorem inp_9697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 9) (closed_mem 9 9) cl_9697 (by decide) v hb
def cl_9700 : CNF.NClause := [(404,true),(410,false),(416,true),(422,true),(423,true),(429,true)]
theorem inp_9700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 9) (closed_mem 9 9) cl_9700 (by decide) v hb
def cl_9701 : CNF.NClause := [(404,false),(410,true),(416,true),(422,true),(423,true),(429,true)]
theorem inp_9701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 9) (closed_mem 9 9) cl_9701 (by decide) v hb
def cl_9703 : CNF.NClause := [(413,true),(414,true),(415,true),(416,true),(417,false),(433,true)]
theorem inp_9703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) cl_9703 (by decide) v hb
def cl_9704 : CNF.NClause := [(413,true),(414,true),(415,true),(416,false),(417,true),(433,true)]
theorem inp_9704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) cl_9704 (by decide) v hb
def cl_9705 : CNF.NClause := [(413,true),(414,true),(415,false),(416,true),(417,true),(433,true)]
theorem inp_9705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) cl_9705 (by decide) v hb
def cl_9706 : CNF.NClause := [(413,true),(414,false),(415,true),(416,true),(417,true),(433,true)]
theorem inp_9706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) cl_9706 (by decide) v hb
def cl_9707 : CNF.NClause := [(413,false),(414,true),(415,true),(416,true),(417,true),(433,true)]
theorem inp_9707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) cl_9707 (by decide) v hb
def cl_9708 : CNF.NClause := [(407,true),(410,true),(413,true),(421,true),(424,true),(431,false)]
theorem inp_9708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) cl_9708 (by decide) v hb
def cl_9709 : CNF.NClause := [(407,true),(410,true),(413,true),(421,true),(424,false),(431,true)]
theorem inp_9709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) cl_9709 (by decide) v hb
def cl_9711 : CNF.NClause := [(407,true),(410,true),(413,false),(421,true),(424,true),(431,true)]
theorem inp_9711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) cl_9711 (by decide) v hb
def cl_9712 : CNF.NClause := [(407,true),(410,false),(413,true),(421,true),(424,true),(431,true)]
theorem inp_9712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) cl_9712 (by decide) v hb
def cl_9713 : CNF.NClause := [(407,false),(410,true),(413,true),(421,true),(424,true),(431,true)]
theorem inp_9713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) cl_9713 (by decide) v hb
def cl_9714 : CNF.NClause := [(405,true),(409,true),(413,true),(422,true),(426,true),(432,false)]
theorem inp_9714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) cl_9714 (by decide) v hb
def cl_9715 : CNF.NClause := [(405,true),(409,true),(413,true),(422,true),(426,false),(432,true)]
theorem inp_9715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) cl_9715 (by decide) v hb
def cl_9716 : CNF.NClause := [(405,true),(409,true),(413,true),(422,false),(426,true),(432,true)]
theorem inp_9716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) cl_9716 (by decide) v hb
def cl_9717 : CNF.NClause := [(405,true),(409,true),(413,false),(422,true),(426,true),(432,true)]
theorem inp_9717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) cl_9717 (by decide) v hb
def cl_9718 : CNF.NClause := [(405,true),(409,false),(413,true),(422,true),(426,true),(432,true)]
theorem inp_9718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) cl_9718 (by decide) v hb
def cl_9719 : CNF.NClause := [(405,false),(409,true),(413,true),(422,true),(426,true),(432,true)]
theorem inp_9719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) cl_9719 (by decide) v hb
def cl_9724 : CNF.NClause := [(406,true),(412,false),(413,true),(419,true),(425,true),(429,true)]
theorem inp_9724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9724 v hb
def cl_9726 : CNF.NClause := [(404,true),(411,true),(413,true),(420,true),(427,true),(430,false)]
theorem inp_9726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) cl_9726 (by decide) v hb
def cl_9727 : CNF.NClause := [(404,true),(411,true),(413,true),(420,true),(427,false),(430,true)]
theorem inp_9727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) cl_9727 (by decide) v hb
def cl_9728 : CNF.NClause := [(404,true),(411,true),(413,true),(420,false),(427,true),(430,true)]
theorem inp_9728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) cl_9728 (by decide) v hb
def cl_9729 : CNF.NClause := [(404,true),(411,true),(413,false),(420,true),(427,true),(430,true)]
theorem inp_9729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) cl_9729 (by decide) v hb
def cl_9731 : CNF.NClause := [(404,false),(411,true),(413,true),(420,true),(427,true),(430,true)]
theorem inp_9731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) cl_9731 (by decide) v hb
end Percolation.NReplay
