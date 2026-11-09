import NInputs195
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12793 : CNF.NClause := [(899,true),(905,true),(911,true),(917,true),(923,false),(925,true)]
theorem inp_12793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 29) (closed_mem 25 29) cl_12793 (by decide) v hb
def cl_12794 : CNF.NClause := [(899,true),(905,true),(911,true),(917,false),(923,true),(925,true)]
theorem inp_12794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 29) (closed_mem 25 29) cl_12794 (by decide) v hb
def cl_12795 : CNF.NClause := [(899,true),(905,true),(911,false),(917,true),(923,true),(925,true)]
theorem inp_12795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 29) (closed_mem 25 29) cl_12795 (by decide) v hb
def cl_12796 : CNF.NClause := [(899,true),(905,false),(911,true),(917,true),(923,true),(925,true)]
theorem inp_12796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 29) (closed_mem 25 29) cl_12796 (by decide) v hb
def cl_12798 : CNF.NClause := [(899,true),(904,true),(909,true),(914,true),(919,true),(924,false)]
theorem inp_12798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 30) (closed_mem 25 30) cl_12798 (by decide) v hb
def cl_12808 : CNF.NClause := [(955,true),(956,false),(957,true),(958,true),(959,true),(960,true)]
theorem inp_12808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 0) (closed_mem 26 0) cl_12808 (by decide) v hb
def cl_12811 : CNF.NClause := [(934,true),(939,true),(944,true),(949,true),(954,false),(955,true)]
theorem inp_12811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 1) (closed_mem 26 1) cl_12811 (by decide) v hb
def cl_12812 : CNF.NClause := [(934,true),(939,true),(944,true),(949,false),(954,true),(955,true)]
theorem inp_12812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 1) (closed_mem 26 1) cl_12812 (by decide) v hb
def cl_12814 : CNF.NClause := [(934,true),(939,false),(944,true),(949,true),(954,true),(955,true)]
theorem inp_12814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 1) (closed_mem 26 1) cl_12814 (by decide) v hb
def cl_12815 : CNF.NClause := [(934,false),(939,true),(944,true),(949,true),(954,true),(955,true)]
theorem inp_12815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 1) (closed_mem 26 1) cl_12815 (by decide) v hb
def cl_12817 : CNF.NClause := [(932,true),(937,true),(942,true),(947,true),(952,false),(955,true)]
theorem inp_12817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 2) (closed_mem 26 2) cl_12817 (by decide) v hb
def cl_12818 : CNF.NClause := [(932,true),(937,true),(942,true),(947,false),(952,true),(955,true)]
theorem inp_12818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 2) (closed_mem 26 2) cl_12818 (by decide) v hb
def cl_12819 : CNF.NClause := [(932,true),(937,true),(942,false),(947,true),(952,true),(955,true)]
theorem inp_12819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 2) (closed_mem 26 2) cl_12819 (by decide) v hb
def cl_12820 : CNF.NClause := [(932,true),(937,false),(942,true),(947,true),(952,true),(955,true)]
theorem inp_12820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 2) (closed_mem 26 2) cl_12820 (by decide) v hb
def cl_12821 : CNF.NClause := [(932,false),(937,true),(942,true),(947,true),(952,true),(955,true)]
theorem inp_12821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 2) (closed_mem 26 2) cl_12821 (by decide) v hb
def cl_12823 : CNF.NClause := [(933,true),(938,true),(943,true),(948,true),(953,false),(955,true)]
theorem inp_12823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 3) (closed_mem 26 3) cl_12823 (by decide) v hb
def cl_12824 : CNF.NClause := [(933,true),(938,true),(943,true),(948,false),(953,true),(955,true)]
theorem inp_12824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 3) (closed_mem 26 3) cl_12824 (by decide) v hb
def cl_12825 : CNF.NClause := [(933,true),(938,true),(943,false),(948,true),(953,true),(955,true)]
theorem inp_12825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 3) (closed_mem 26 3) cl_12825 (by decide) v hb
def cl_12826 : CNF.NClause := [(933,true),(938,false),(943,true),(948,true),(953,true),(955,true)]
theorem inp_12826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 3) (closed_mem 26 3) cl_12826 (by decide) v hb
def cl_12829 : CNF.NClause := [(931,true),(936,true),(941,true),(946,true),(951,false),(955,true)]
theorem inp_12829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 4) (closed_mem 26 4) cl_12829 (by decide) v hb
def cl_12830 : CNF.NClause := [(931,true),(936,true),(941,true),(946,false),(951,true),(955,true)]
theorem inp_12830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 4) (closed_mem 26 4) cl_12830 (by decide) v hb
def cl_12831 : CNF.NClause := [(931,true),(936,true),(941,false),(946,true),(951,true),(955,true)]
theorem inp_12831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 4) (closed_mem 26 4) cl_12831 (by decide) v hb
def cl_12832 : CNF.NClause := [(931,true),(936,false),(941,true),(946,true),(951,true),(955,true)]
theorem inp_12832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 4) (closed_mem 26 4) cl_12832 (by decide) v hb
def cl_12833 : CNF.NClause := [(931,false),(936,true),(941,true),(946,true),(951,true),(955,true)]
theorem inp_12833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 4) (closed_mem 26 4) cl_12833 (by decide) v hb
def cl_12835 : CNF.NClause := [(950,true),(951,true),(952,true),(953,true),(954,false),(960,true)]
theorem inp_12835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 5) (closed_mem 26 5) cl_12835 (by decide) v hb
def cl_12836 : CNF.NClause := [(950,true),(951,true),(952,true),(953,false),(954,true),(960,true)]
theorem inp_12836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 5) (closed_mem 26 5) cl_12836 (by decide) v hb
def cl_12838 : CNF.NClause := [(950,true),(951,false),(952,true),(953,true),(954,true),(960,true)]
theorem inp_12838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 5) (closed_mem 26 5) cl_12838 (by decide) v hb
def cl_12839 : CNF.NClause := [(950,false),(951,true),(952,true),(953,true),(954,true),(960,true)]
theorem inp_12839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 5) (closed_mem 26 5) cl_12839 (by decide) v hb
def cl_12840 : CNF.NClause := [(934,true),(938,true),(942,true),(946,true),(950,true),(959,false)]
theorem inp_12840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 6) (closed_mem 26 6) cl_12840 (by decide) v hb
def cl_12841 : CNF.NClause := [(934,true),(938,true),(942,true),(946,true),(950,false),(959,true)]
theorem inp_12841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 6) (closed_mem 26 6) cl_12841 (by decide) v hb
def cl_12842 : CNF.NClause := [(934,true),(938,true),(942,true),(946,false),(950,true),(959,true)]
theorem inp_12842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 6) (closed_mem 26 6) cl_12842 (by decide) v hb
def cl_12845 : CNF.NClause := [(934,false),(938,true),(942,true),(946,true),(950,true),(959,true)]
theorem inp_12845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 6) (closed_mem 26 6) cl_12845 (by decide) v hb
def cl_12846 : CNF.NClause := [(932,true),(939,true),(941,true),(948,true),(950,true),(957,false)]
theorem inp_12846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 7) (closed_mem 26 7) cl_12846 (by decide) v hb
def cl_12847 : CNF.NClause := [(932,true),(939,true),(941,true),(948,true),(950,false),(957,true)]
theorem inp_12847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 7) (closed_mem 26 7) cl_12847 (by decide) v hb
def cl_12849 : CNF.NClause := [(932,true),(939,true),(941,false),(948,true),(950,true),(957,true)]
theorem inp_12849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 7) (closed_mem 26 7) cl_12849 (by decide) v hb
def cl_12851 : CNF.NClause := [(932,false),(939,true),(941,true),(948,true),(950,true),(957,true)]
theorem inp_12851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 7) (closed_mem 26 7) cl_12851 (by decide) v hb
def cl_12855 : CNF.NClause := [(933,true),(936,true),(944,false),(947,true),(950,true),(958,true)]
theorem inp_12855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 8) (closed_mem 26 8) cl_12855 (by decide) v hb
def cl_12858 : CNF.NClause := [(931,true),(937,true),(943,true),(949,true),(950,true),(956,false)]
theorem inp_12858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 9) (closed_mem 26 9) cl_12858 (by decide) v hb
def cl_12866 : CNF.NClause := [(940,true),(941,true),(942,true),(943,false),(944,true),(960,true)]
theorem inp_12866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 10) (closed_mem 26 10) cl_12866 (by decide) v hb
def cl_12867 : CNF.NClause := [(940,true),(941,true),(942,false),(943,true),(944,true),(960,true)]
theorem inp_12867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 10) (closed_mem 26 10) cl_12867 (by decide) v hb
def cl_12868 : CNF.NClause := [(940,true),(941,false),(942,true),(943,true),(944,true),(960,true)]
theorem inp_12868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 10) (closed_mem 26 10) cl_12868 (by decide) v hb
def cl_12869 : CNF.NClause := [(940,false),(941,true),(942,true),(943,true),(944,true),(960,true)]
theorem inp_12869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 10) (closed_mem 26 10) cl_12869 (by decide) v hb
def cl_12870 : CNF.NClause := [(934,true),(937,true),(940,true),(948,true),(951,true),(958,false)]
theorem inp_12870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 11) (closed_mem 26 11) cl_12870 (by decide) v hb
def cl_12871 : CNF.NClause := [(934,true),(937,true),(940,true),(948,true),(951,false),(958,true)]
theorem inp_12871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 11) (closed_mem 26 11) cl_12871 (by decide) v hb
def cl_12873 : CNF.NClause := [(934,true),(937,true),(940,false),(948,true),(951,true),(958,true)]
theorem inp_12873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 11) (closed_mem 26 11) cl_12873 (by decide) v hb
def cl_12874 : CNF.NClause := [(934,true),(937,false),(940,true),(948,true),(951,true),(958,true)]
theorem inp_12874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 11) (closed_mem 26 11) cl_12874 (by decide) v hb
def cl_12875 : CNF.NClause := [(934,false),(937,true),(940,true),(948,true),(951,true),(958,true)]
theorem inp_12875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 11) (closed_mem 26 11) cl_12875 (by decide) v hb
def cl_12877 : CNF.NClause := [(932,true),(936,true),(940,true),(949,true),(953,false),(959,true)]
theorem inp_12877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 12) (closed_mem 26 12) cl_12877 (by decide) v hb
def cl_12879 : CNF.NClause := [(932,true),(936,true),(940,false),(949,true),(953,true),(959,true)]
theorem inp_12879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 12) (closed_mem 26 12) cl_12879 (by decide) v hb
def cl_12882 : CNF.NClause := [(933,true),(939,true),(940,true),(946,true),(952,true),(956,false)]
theorem inp_12882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 13) (closed_mem 26 13) cl_12882 (by decide) v hb
end Percolation.NReplay
