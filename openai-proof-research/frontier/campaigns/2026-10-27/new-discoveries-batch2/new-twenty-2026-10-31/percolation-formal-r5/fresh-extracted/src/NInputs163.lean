import NInputs162
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9926 : CNF.NClause := [(438,true),(440,true),(447,true),(449,false),(456,true),(461,true)]
theorem inp_9926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 16) (closed_mem 10 16) cl_9926 (by decide) v hb
def cl_9927 : CNF.NClause := [(438,true),(440,true),(447,false),(449,true),(456,true),(461,true)]
theorem inp_9927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 16) (closed_mem 10 16) cl_9927 (by decide) v hb
def cl_9929 : CNF.NClause := [(438,false),(440,true),(447,true),(449,true),(456,true),(461,true)]
theorem inp_9929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 16) (closed_mem 10 16) cl_9929 (by decide) v hb
def cl_9932 : CNF.NClause := [(436,true),(442,true),(448,true),(449,false),(455,true),(460,true)]
theorem inp_9932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9932 v hb
def cl_9936 : CNF.NClause := [(437,true),(441,true),(445,true),(449,true),(458,true),(463,false)]
theorem inp_9936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 18) (closed_mem 10 18) cl_9936 (by decide) v hb
def cl_9941 : CNF.NClause := [(437,false),(441,true),(445,true),(449,true),(458,true),(463,true)]
theorem inp_9941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 18) (closed_mem 10 18) cl_9941 (by decide) v hb
def cl_9943 : CNF.NClause := [(435,true),(443,true),(446,true),(449,true),(457,false),(462,true)]
theorem inp_9943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 19) (closed_mem 10 19) cl_9943 (by decide) v hb
def cl_9947 : CNF.NClause := [(435,false),(443,true),(446,true),(449,true),(457,true),(462,true)]
theorem inp_9947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 19) (closed_mem 10 19) cl_9947 (by decide) v hb
def cl_9949 : CNF.NClause := [(439,true),(440,true),(441,true),(442,true),(443,false),(464,true)]
theorem inp_9949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 20) (closed_mem 10 20) cl_9949 (by decide) v hb
def cl_9950 : CNF.NClause := [(439,true),(440,true),(441,true),(442,false),(443,true),(464,true)]
theorem inp_9950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 20) (closed_mem 10 20) cl_9950 (by decide) v hb
def cl_9951 : CNF.NClause := [(439,true),(440,true),(441,false),(442,true),(443,true),(464,true)]
theorem inp_9951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 20) (closed_mem 10 20) cl_9951 (by decide) v hb
def cl_9952 : CNF.NClause := [(439,true),(440,false),(441,true),(442,true),(443,true),(464,true)]
theorem inp_9952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 20) (closed_mem 10 20) cl_9952 (by decide) v hb
def cl_9953 : CNF.NClause := [(439,false),(440,true),(441,true),(442,true),(443,true),(464,true)]
theorem inp_9953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 20) (closed_mem 10 20) cl_9953 (by decide) v hb
def cl_9957 : CNF.NClause := [(438,true),(439,true),(445,false),(451,true),(457,true),(460,true)]
theorem inp_9957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 21) (closed_mem 10 21) cl_9957 (by decide) v hb
def cl_9958 : CNF.NClause := [(438,true),(439,false),(445,true),(451,true),(457,true),(460,true)]
theorem inp_9958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 21) (closed_mem 10 21) cl_9958 (by decide) v hb
def cl_9960 : CNF.NClause := [(436,true),(439,true),(447,true),(450,true),(458,true),(462,false)]
theorem inp_9960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 22) (closed_mem 10 22) cl_9960 (by decide) v hb
def cl_9962 : CNF.NClause := [(436,true),(439,true),(447,true),(450,false),(458,true),(462,true)]
theorem inp_9962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 22) (closed_mem 10 22) cl_9962 (by decide) v hb
def cl_9964 : CNF.NClause := [(436,true),(439,false),(447,true),(450,true),(458,true),(462,true)]
theorem inp_9964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 22) (closed_mem 10 22) cl_9964 (by decide) v hb
def cl_9968 : CNF.NClause := [(437,true),(439,true),(446,true),(453,false),(455,true),(461,true)]
theorem inp_9968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 23) (closed_mem 10 23) cl_9968 (by decide) v hb
def cl_9970 : CNF.NClause := [(437,true),(439,false),(446,true),(453,true),(455,true),(461,true)]
theorem inp_9970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 23) (closed_mem 10 23) cl_9970 (by decide) v hb
def cl_9971 : CNF.NClause := [(437,false),(439,true),(446,true),(453,true),(455,true),(461,true)]
theorem inp_9971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 23) (closed_mem 10 23) cl_9971 (by decide) v hb
def cl_9973 : CNF.NClause := [(435,true),(439,true),(448,true),(452,true),(456,false),(463,true)]
theorem inp_9973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 24) (closed_mem 10 24) cl_9973 (by decide) v hb
def cl_9975 : CNF.NClause := [(435,true),(439,true),(448,false),(452,true),(456,true),(463,true)]
theorem inp_9975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 24) (closed_mem 10 24) cl_9975 (by decide) v hb
def cl_9976 : CNF.NClause := [(435,true),(439,false),(448,true),(452,true),(456,true),(463,true)]
theorem inp_9976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 24) (closed_mem 10 24) cl_9976 (by decide) v hb
def cl_9980 : CNF.NClause := [(434,true),(435,true),(436,true),(437,false),(438,true),(464,true)]
theorem inp_9980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 25) (closed_mem 10 25) cl_9980 (by decide) v hb
def cl_9981 : CNF.NClause := [(434,true),(435,true),(436,false),(437,true),(438,true),(464,true)]
theorem inp_9981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 25) (closed_mem 10 25) cl_9981 (by decide) v hb
def cl_9982 : CNF.NClause := [(434,true),(435,false),(436,true),(437,true),(438,true),(464,true)]
theorem inp_9982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9982 v hb
def cl_9984 : CNF.NClause := [(434,true),(443,true),(447,true),(451,true),(455,true),(463,false)]
theorem inp_9984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 26) (closed_mem 10 26) cl_9984 (by decide) v hb
def cl_9985 : CNF.NClause := [(434,true),(443,true),(447,true),(451,true),(455,false),(463,true)]
theorem inp_9985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 26) (closed_mem 10 26) cl_9985 (by decide) v hb
def cl_9986 : CNF.NClause := [(434,true),(443,true),(447,true),(451,false),(455,true),(463,true)]
theorem inp_9986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 26) (closed_mem 10 26) cl_9986 (by decide) v hb
def cl_9987 : CNF.NClause := [(434,true),(443,true),(447,false),(451,true),(455,true),(463,true)]
theorem inp_9987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9987 v hb
def cl_9990 : CNF.NClause := [(434,true),(441,true),(448,true),(450,true),(457,true),(461,false)]
theorem inp_9990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 27) (closed_mem 10 27) cl_9990 (by decide) v hb
def cl_9991 : CNF.NClause := [(434,true),(441,true),(448,true),(450,true),(457,false),(461,true)]
theorem inp_9991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 27) (closed_mem 10 27) cl_9991 (by decide) v hb
def cl_9993 : CNF.NClause := [(434,true),(441,true),(448,false),(450,true),(457,true),(461,true)]
theorem inp_9993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 27) (closed_mem 10 27) cl_9993 (by decide) v hb
def cl_9994 : CNF.NClause := [(434,true),(441,false),(448,true),(450,true),(457,true),(461,true)]
theorem inp_9994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 27) (closed_mem 10 27) cl_9994 (by decide) v hb
def cl_9996 : CNF.NClause := [(434,true),(442,true),(445,true),(453,true),(456,true),(462,false)]
theorem inp_9996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 28) (closed_mem 10 28) cl_9996 (by decide) v hb
def cl_9997 : CNF.NClause := [(434,true),(442,true),(445,true),(453,true),(456,false),(462,true)]
theorem inp_9997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9997 v hb
def cl_9998 : CNF.NClause := [(434,true),(442,true),(445,true),(453,false),(456,true),(462,true)]
theorem inp_9998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 28) (closed_mem 10 28) cl_9998 (by decide) v hb
def cl_9999 : CNF.NClause := [(434,true),(442,true),(445,false),(453,true),(456,true),(462,true)]
theorem inp_9999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 28) (closed_mem 10 28) cl_9999 (by decide) v hb
def cl_10000 : CNF.NClause := [(434,true),(442,false),(445,true),(453,true),(456,true),(462,true)]
theorem inp_10000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 28) (closed_mem 10 28) cl_10000 (by decide) v hb
def cl_10002 : CNF.NClause := [(434,true),(440,true),(446,true),(452,true),(458,true),(460,false)]
theorem inp_10002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 29) (closed_mem 10 29) cl_10002 (by decide) v hb
def cl_10006 : CNF.NClause := [(434,true),(440,false),(446,true),(452,true),(458,true),(460,true)]
theorem inp_10006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 29) (closed_mem 10 29) cl_10006 (by decide) v hb
def cl_10011 : CNF.NClause := [(434,true),(439,true),(444,false),(449,true),(454,true),(459,true)]
theorem inp_10011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 30) (closed_mem 10 30) cl_10011 (by decide) v hb
def cl_10015 : CNF.NClause := [(490,true),(491,true),(492,true),(493,true),(494,false),(495,true)]
theorem inp_10015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 0) (closed_mem 11 0) cl_10015 (by decide) v hb
def cl_10016 : CNF.NClause := [(490,true),(491,true),(492,true),(493,false),(494,true),(495,true)]
theorem inp_10016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 0) (closed_mem 11 0) cl_10016 (by decide) v hb
def cl_10017 : CNF.NClause := [(490,true),(491,true),(492,false),(493,true),(494,true),(495,true)]
theorem inp_10017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 0) (closed_mem 11 0) cl_10017 (by decide) v hb
def cl_10018 : CNF.NClause := [(490,true),(491,false),(492,true),(493,true),(494,true),(495,true)]
theorem inp_10018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 0) (closed_mem 11 0) cl_10018 (by decide) v hb
def cl_10021 : CNF.NClause := [(469,true),(474,true),(479,true),(484,true),(489,false),(490,true)]
theorem inp_10021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 1) (closed_mem 11 1) cl_10021 (by decide) v hb
def cl_10022 : CNF.NClause := [(469,true),(474,true),(479,true),(484,false),(489,true),(490,true)]
theorem inp_10022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 1) (closed_mem 11 1) cl_10022 (by decide) v hb
def cl_10023 : CNF.NClause := [(469,true),(474,true),(479,false),(484,true),(489,true),(490,true)]
theorem inp_10023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 1) (closed_mem 11 1) cl_10023 (by decide) v hb
end Percolation.NReplay
