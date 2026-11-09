import NInputs161
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9811 : CNF.NClause := [(403,true),(411,true),(414,true),(422,true),(425,false),(431,true)]
theorem inp_9811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) cl_9811 (by decide) v hb
def cl_9812 : CNF.NClause := [(403,true),(411,true),(414,true),(422,false),(425,true),(431,true)]
theorem inp_9812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) cl_9812 (by decide) v hb
def cl_9813 : CNF.NClause := [(403,true),(411,true),(414,false),(422,true),(425,true),(431,true)]
theorem inp_9813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) cl_9813 (by decide) v hb
def cl_9814 : CNF.NClause := [(403,true),(411,false),(414,true),(422,true),(425,true),(431,true)]
theorem inp_9814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) cl_9814 (by decide) v hb
def cl_9816 : CNF.NClause := [(403,true),(409,true),(415,true),(421,true),(427,true),(429,false)]
theorem inp_9816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) cl_9816 (by decide) v hb
def cl_9817 : CNF.NClause := [(403,true),(409,true),(415,true),(421,true),(427,false),(429,true)]
theorem inp_9817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) cl_9817 (by decide) v hb
def cl_9818 : CNF.NClause := [(403,true),(409,true),(415,true),(421,false),(427,true),(429,true)]
theorem inp_9818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) cl_9818 (by decide) v hb
def cl_9819 : CNF.NClause := [(403,true),(409,true),(415,false),(421,true),(427,true),(429,true)]
theorem inp_9819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) cl_9819 (by decide) v hb
def cl_9820 : CNF.NClause := [(403,true),(409,false),(415,true),(421,true),(427,true),(429,true)]
theorem inp_9820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9820 v hb
def cl_9823 : CNF.NClause := [(403,true),(408,true),(413,true),(418,true),(423,false),(428,true)]
theorem inp_9823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 30) (closed_mem 9 30) cl_9823 (by decide) v hb
def cl_9824 : CNF.NClause := [(403,true),(408,true),(413,true),(418,false),(423,true),(428,true)]
theorem inp_9824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 30) (closed_mem 9 30) cl_9824 (by decide) v hb
def cl_9825 : CNF.NClause := [(403,true),(408,true),(413,false),(418,true),(423,true),(428,true)]
theorem inp_9825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 30) (closed_mem 9 30) cl_9825 (by decide) v hb
def cl_9826 : CNF.NClause := [(403,true),(408,false),(413,true),(418,true),(423,true),(428,true)]
theorem inp_9826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 30) (closed_mem 9 30) cl_9826 (by decide) v hb
def cl_9829 : CNF.NClause := [(459,true),(460,true),(461,true),(462,true),(463,false),(464,true)]
theorem inp_9829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 0) (closed_mem 10 0) cl_9829 (by decide) v hb
def cl_9830 : CNF.NClause := [(459,true),(460,true),(461,true),(462,false),(463,true),(464,true)]
theorem inp_9830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 0) (closed_mem 10 0) cl_9830 (by decide) v hb
def cl_9831 : CNF.NClause := [(459,true),(460,true),(461,false),(462,true),(463,true),(464,true)]
theorem inp_9831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 0) (closed_mem 10 0) cl_9831 (by decide) v hb
def cl_9832 : CNF.NClause := [(459,true),(460,false),(461,true),(462,true),(463,true),(464,true)]
theorem inp_9832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 0) (closed_mem 10 0) cl_9832 (by decide) v hb
def cl_9835 : CNF.NClause := [(438,true),(443,true),(448,true),(453,true),(458,false),(459,true)]
theorem inp_9835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 1) (closed_mem 10 1) cl_9835 (by decide) v hb
def cl_9837 : CNF.NClause := [(438,true),(443,true),(448,false),(453,true),(458,true),(459,true)]
theorem inp_9837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 1) (closed_mem 10 1) cl_9837 (by decide) v hb
def cl_9838 : CNF.NClause := [(438,true),(443,false),(448,true),(453,true),(458,true),(459,true)]
theorem inp_9838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 1) (closed_mem 10 1) cl_9838 (by decide) v hb
def cl_9839 : CNF.NClause := [(438,false),(443,true),(448,true),(453,true),(458,true),(459,true)]
theorem inp_9839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 1) (closed_mem 10 1) cl_9839 (by decide) v hb
def cl_9841 : CNF.NClause := [(436,true),(441,true),(446,true),(451,true),(456,false),(459,true)]
theorem inp_9841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 2) (closed_mem 10 2) cl_9841 (by decide) v hb
def cl_9842 : CNF.NClause := [(436,true),(441,true),(446,true),(451,false),(456,true),(459,true)]
theorem inp_9842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 2) (closed_mem 10 2) cl_9842 (by decide) v hb
def cl_9849 : CNF.NClause := [(437,true),(442,true),(447,false),(452,true),(457,true),(459,true)]
theorem inp_9849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 3) (closed_mem 10 3) cl_9849 (by decide) v hb
def cl_9855 : CNF.NClause := [(435,true),(440,true),(445,false),(450,true),(455,true),(459,true)]
theorem inp_9855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9855 v hb
def cl_9856 : CNF.NClause := [(435,true),(440,false),(445,true),(450,true),(455,true),(459,true)]
theorem inp_9856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 4) (closed_mem 10 4) cl_9856 (by decide) v hb
def cl_9857 : CNF.NClause := [(435,false),(440,true),(445,true),(450,true),(455,true),(459,true)]
theorem inp_9857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 4) (closed_mem 10 4) cl_9857 (by decide) v hb
def cl_9859 : CNF.NClause := [(454,true),(455,true),(456,true),(457,true),(458,false),(464,true)]
theorem inp_9859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 5) (closed_mem 10 5) cl_9859 (by decide) v hb
def cl_9860 : CNF.NClause := [(454,true),(455,true),(456,true),(457,false),(458,true),(464,true)]
theorem inp_9860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9860 v hb
def cl_9863 : CNF.NClause := [(454,false),(455,true),(456,true),(457,true),(458,true),(464,true)]
theorem inp_9863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 5) (closed_mem 10 5) cl_9863 (by decide) v hb
def cl_9864 : CNF.NClause := [(438,true),(442,true),(446,true),(450,true),(454,true),(463,false)]
theorem inp_9864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) cl_9864 (by decide) v hb
def cl_9865 : CNF.NClause := [(438,true),(442,true),(446,true),(450,true),(454,false),(463,true)]
theorem inp_9865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) cl_9865 (by decide) v hb
def cl_9866 : CNF.NClause := [(438,true),(442,true),(446,true),(450,false),(454,true),(463,true)]
theorem inp_9866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) cl_9866 (by decide) v hb
def cl_9867 : CNF.NClause := [(438,true),(442,true),(446,false),(450,true),(454,true),(463,true)]
theorem inp_9867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) cl_9867 (by decide) v hb
def cl_9868 : CNF.NClause := [(438,true),(442,false),(446,true),(450,true),(454,true),(463,true)]
theorem inp_9868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) cl_9868 (by decide) v hb
def cl_9871 : CNF.NClause := [(436,true),(443,true),(445,true),(452,true),(454,false),(461,true)]
theorem inp_9871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) cl_9871 (by decide) v hb
def cl_9872 : CNF.NClause := [(436,true),(443,true),(445,true),(452,false),(454,true),(461,true)]
theorem inp_9872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9872 v hb
def cl_9874 : CNF.NClause := [(436,true),(443,false),(445,true),(452,true),(454,true),(461,true)]
theorem inp_9874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) cl_9874 (by decide) v hb
def cl_9875 : CNF.NClause := [(436,false),(443,true),(445,true),(452,true),(454,true),(461,true)]
theorem inp_9875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) cl_9875 (by decide) v hb
def cl_9877 : CNF.NClause := [(437,true),(440,true),(448,true),(451,true),(454,false),(462,true)]
theorem inp_9877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 8) (closed_mem 10 8) cl_9877 (by decide) v hb
def cl_9883 : CNF.NClause := [(435,true),(441,true),(447,true),(453,true),(454,false),(460,true)]
theorem inp_9883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9883 v hb
def cl_9887 : CNF.NClause := [(435,false),(441,true),(447,true),(453,true),(454,true),(460,true)]
theorem inp_9887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 9) (closed_mem 10 9) cl_9887 (by decide) v hb
def cl_9893 : CNF.NClause := [(444,false),(445,true),(446,true),(447,true),(448,true),(464,true)]
theorem inp_9893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 10) (closed_mem 10 10) cl_9893 (by decide) v hb
def cl_9897 : CNF.NClause := [(438,true),(441,true),(444,false),(452,true),(455,true),(462,true)]
theorem inp_9897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 11) (closed_mem 10 11) cl_9897 (by decide) v hb
def cl_9903 : CNF.NClause := [(436,true),(440,true),(444,false),(453,true),(457,true),(463,true)]
theorem inp_9903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9903 v hb
def cl_9909 : CNF.NClause := [(437,true),(443,true),(444,false),(450,true),(456,true),(460,true)]
theorem inp_9909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 13) (closed_mem 10 13) cl_9909 (by decide) v hb
def cl_9915 : CNF.NClause := [(435,true),(442,true),(444,false),(451,true),(458,true),(461,true)]
theorem inp_9915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 14) (closed_mem 10 14) cl_9915 (by decide) v hb
def cl_9920 : CNF.NClause := [(449,true),(450,true),(451,true),(452,false),(453,true),(464,true)]
theorem inp_9920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 15) (closed_mem 10 15) cl_9920 (by decide) v hb
def cl_9923 : CNF.NClause := [(449,false),(450,true),(451,true),(452,true),(453,true),(464,true)]
theorem inp_9923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 15) (closed_mem 10 15) cl_9923 (by decide) v hb
def cl_9924 : CNF.NClause := [(438,true),(440,true),(447,true),(449,true),(456,true),(461,false)]
theorem inp_9924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 16) (closed_mem 10 16) cl_9924 (by decide) v hb
end Percolation.NReplay
