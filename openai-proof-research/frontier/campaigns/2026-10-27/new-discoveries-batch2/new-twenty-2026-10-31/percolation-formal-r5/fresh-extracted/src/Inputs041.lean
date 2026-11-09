import Inputs040
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9615 : CNF.NClause := [(372,true),(381,true),(385,false),(389,true),(393,true),(401,true)]
theorem inp_9615 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9615 := by
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) cl_9615 (by decide) v h
def cl_9646 : CNF.NClause := [(428,true),(429,false),(430,true),(431,true),(432,true),(433,true)]
theorem inp_9646 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9646 := by
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) cl_9646 (by decide) v h
def cl_9654 : CNF.NClause := [(405,true),(410,true),(415,true),(420,true),(425,true),(428,false)]
theorem inp_9654 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9654 := by
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) cl_9654 (by decide) v h
def cl_9675 : CNF.NClause := [(423,true),(424,true),(425,false),(426,true),(427,true),(433,true)]
theorem inp_9675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9675 := by
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) cl_9675 (by decide) v h
def cl_9679 : CNF.NClause := [(407,true),(411,true),(415,true),(419,true),(423,false),(432,true)]
theorem inp_9679 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9679 := by
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) cl_9679 (by decide) v h
def cl_9683 : CNF.NClause := [(407,false),(411,true),(415,true),(419,true),(423,true),(432,true)]
theorem inp_9683 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9683 := by
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) cl_9683 (by decide) v h
def cl_9694 : CNF.NClause := [(406,true),(409,false),(417,true),(420,true),(423,true),(431,true)]
theorem inp_9694 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9694 := by
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) cl_9694 (by decide) v h
def cl_9724 : CNF.NClause := [(406,true),(412,false),(413,true),(419,true),(425,true),(429,true)]
theorem inp_9724 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9724 := by
  exact input_gate (closedGate5 9 13) (closed_mem 9 13) cl_9724 (by decide) v h
def cl_9820 : CNF.NClause := [(403,true),(409,false),(415,true),(421,true),(427,true),(429,true)]
theorem inp_9820 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9820 := by
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) cl_9820 (by decide) v h
def cl_9827 : CNF.NClause := [(403,false),(408,true),(413,true),(418,true),(423,true),(428,true)]
theorem inp_9827 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9827 := by
  exact input_gate (closedGate5 9 30) (closed_mem 9 30) cl_9827 (by decide) v h
def cl_9855 : CNF.NClause := [(435,true),(440,true),(445,false),(450,true),(455,true),(459,true)]
theorem inp_9855 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9855 := by
  exact input_gate (closedGate5 10 4) (closed_mem 10 4) cl_9855 (by decide) v h
def cl_9860 : CNF.NClause := [(454,true),(455,true),(456,true),(457,false),(458,true),(464,true)]
theorem inp_9860 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9860 := by
  exact input_gate (closedGate5 10 5) (closed_mem 10 5) cl_9860 (by decide) v h
def cl_9869 : CNF.NClause := [(438,false),(442,true),(446,true),(450,true),(454,true),(463,true)]
theorem inp_9869 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9869 := by
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) cl_9869 (by decide) v h
def cl_9872 : CNF.NClause := [(436,true),(443,true),(445,true),(452,false),(454,true),(461,true)]
theorem inp_9872 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9872 := by
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) cl_9872 (by decide) v h
def cl_9883 : CNF.NClause := [(435,true),(441,true),(447,true),(453,true),(454,false),(460,true)]
theorem inp_9883 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9883 := by
  exact input_gate (closedGate5 10 9) (closed_mem 10 9) cl_9883 (by decide) v h
def cl_9903 : CNF.NClause := [(436,true),(440,true),(444,false),(453,true),(457,true),(463,true)]
theorem inp_9903 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9903 := by
  exact input_gate (closedGate5 10 12) (closed_mem 10 12) cl_9903 (by decide) v h
def cl_9932 : CNF.NClause := [(436,true),(442,true),(448,true),(449,false),(455,true),(460,true)]
theorem inp_9932 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9932 := by
  exact input_gate (closedGate5 10 17) (closed_mem 10 17) cl_9932 (by decide) v h
def cl_9937 : CNF.NClause := [(437,true),(441,true),(445,true),(449,true),(458,false),(463,true)]
theorem inp_9937 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9937 := by
  exact input_gate (closedGate5 10 18) (closed_mem 10 18) cl_9937 (by decide) v h
def cl_9955 : CNF.NClause := [(438,true),(439,true),(445,true),(451,true),(457,false),(460,true)]
theorem inp_9955 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9955 := by
  exact input_gate (closedGate5 10 21) (closed_mem 10 21) cl_9955 (by decide) v h
def cl_9963 : CNF.NClause := [(436,true),(439,true),(447,false),(450,true),(458,true),(462,true)]
theorem inp_9963 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9963 := by
  exact input_gate (closedGate5 10 22) (closed_mem 10 22) cl_9963 (by decide) v h
def cl_9979 : CNF.NClause := [(434,true),(435,true),(436,true),(437,true),(438,false),(464,true)]
theorem inp_9979 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9979 := by
  exact input_gate (closedGate5 10 25) (closed_mem 10 25) cl_9979 (by decide) v h
def cl_9982 : CNF.NClause := [(434,true),(435,false),(436,true),(437,true),(438,true),(464,true)]
theorem inp_9982 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9982 := by
  exact input_gate (closedGate5 10 25) (closed_mem 10 25) cl_9982 (by decide) v h
def cl_9987 : CNF.NClause := [(434,true),(443,true),(447,false),(451,true),(455,true),(463,true)]
theorem inp_9987 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9987 := by
  exact input_gate (closedGate5 10 26) (closed_mem 10 26) cl_9987 (by decide) v h
def cl_9997 : CNF.NClause := [(434,true),(442,true),(445,true),(453,true),(456,false),(462,true)]
theorem inp_9997 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9997 := by
  exact input_gate (closedGate5 10 28) (closed_mem 10 28) cl_9997 (by decide) v h
def cl_10078 : CNF.NClause := [(475,true),(476,false),(477,true),(478,true),(479,true),(495,true)]
theorem inp_10078 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10078 := by
  exact input_gate (closedGate5 11 10) (closed_mem 11 10) cl_10078 (by decide) v h
def cl_10082 : CNF.NClause := [(469,true),(472,true),(475,true),(483,false),(486,true),(493,true)]
theorem inp_10082 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10082 := by
  exact input_gate (closedGate5 11 11) (closed_mem 11 11) cl_10082 (by decide) v h
def cl_10103 : CNF.NClause := [(466,false),(473,true),(475,true),(482,true),(489,true),(492,true)]
theorem inp_10103 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10103 := by
  exact input_gate (closedGate5 11 14) (closed_mem 11 14) cl_10103 (by decide) v h
def cl_10125 : CNF.NClause := [(468,true),(472,true),(476,false),(480,true),(489,true),(494,true)]
theorem inp_10125 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10125 := by
  exact input_gate (closedGate5 11 18) (closed_mem 11 18) cl_10125 (by decide) v h
def cl_10130 : CNF.NClause := [(466,true),(474,true),(477,true),(480,false),(488,true),(493,true)]
theorem inp_10130 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10130 := by
  exact input_gate (closedGate5 11 19) (closed_mem 11 19) cl_10130 (by decide) v h
def cl_10133 : CNF.NClause := [(466,false),(474,true),(477,true),(480,true),(488,true),(493,true)]
theorem inp_10133 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10133 := by
  exact input_gate (closedGate5 11 19) (closed_mem 11 19) cl_10133 (by decide) v h
def cl_10147 : CNF.NClause := [(467,true),(470,true),(478,true),(481,true),(489,false),(493,true)]
theorem inp_10147 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10147 := by
  exact input_gate (closedGate5 11 22) (closed_mem 11 22) cl_10147 (by decide) v h
def cl_10155 : CNF.NClause := [(468,true),(470,true),(477,false),(484,true),(486,true),(492,true)]
theorem inp_10155 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10155 := by
  exact input_gate (closedGate5 11 23) (closed_mem 11 23) cl_10155 (by decide) v h
def cl_11161 : CNF.NClause := [(671,true),(672,true),(673,true),(674,true),(675,false),(681,true)]
theorem inp_11161 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11161 := by
  exact input_gate (closedGate5 17 5) (closed_mem 17 5) cl_11161 (by decide) v h
def cl_11204 : CNF.NClause := [(653,true),(657,true),(661,true),(670,false),(674,true),(680,true)]
theorem inp_11204 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11204 := by
  exact input_gate (closedGate5 17 12) (closed_mem 17 12) cl_11204 (by decide) v h
def cl_11207 : CNF.NClause := [(653,false),(657,true),(661,true),(670,true),(674,true),(680,true)]
theorem inp_11207 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11207 := by
  exact input_gate (closedGate5 17 12) (closed_mem 17 12) cl_11207 (by decide) v h
def cl_11265 : CNF.NClause := [(653,true),(656,true),(664,false),(667,true),(675,true),(679,true)]
theorem inp_11265 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11265 := by
  exact input_gate (closedGate5 17 22) (closed_mem 17 22) cl_11265 (by decide) v h
def cl_11318 : CNF.NClause := [(707,true),(708,true),(709,true),(710,false),(711,true),(712,true)]
theorem inp_11318 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11318 := by
  exact input_gate (closedGate5 18 0) (closed_mem 18 0) cl_11318 (by decide) v h
def cl_11321 : CNF.NClause := [(707,false),(708,true),(709,true),(710,true),(711,true),(712,true)]
theorem inp_11321 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11321 := by
  exact input_gate (closedGate5 18 0) (closed_mem 18 0) cl_11321 (by decide) v h
def cl_11322 : CNF.NClause := [(686,true),(691,true),(696,true),(701,true),(706,true),(707,false)]
theorem inp_11322 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11322 := by
  exact input_gate (closedGate5 18 1) (closed_mem 18 1) cl_11322 (by decide) v h
def cl_11341 : CNF.NClause := [(683,true),(688,true),(693,true),(698,true),(703,false),(707,true)]
theorem inp_11341 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11341 := by
  exact input_gate (closedGate5 18 4) (closed_mem 18 4) cl_11341 (by decide) v h
def cl_11374 : CNF.NClause := [(683,true),(689,false),(695,true),(701,true),(702,true),(708,true)]
theorem inp_11374 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11374 := by
  exact input_gate (closedGate5 18 9) (closed_mem 18 9) cl_11374 (by decide) v h
def cl_11384 : CNF.NClause := [(686,true),(689,true),(692,true),(700,false),(703,true),(710,true)]
theorem inp_11384 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11384 := by
  exact input_gate (closedGate5 18 11) (closed_mem 18 11) cl_11384 (by decide) v h
def cl_11393 : CNF.NClause := [(684,false),(688,true),(692,true),(701,true),(705,true),(711,true)]
theorem inp_11393 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11393 := by
  exact input_gate (closedGate5 18 12) (closed_mem 18 12) cl_11393 (by decide) v h
def cl_11401 : CNF.NClause := [(683,true),(690,true),(692,true),(699,true),(706,false),(709,true)]
theorem inp_11401 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11401 := by
  exact input_gate (closedGate5 18 14) (closed_mem 18 14) cl_11401 (by decide) v h
def cl_11476 : CNF.NClause := [(682,true),(691,false),(695,true),(699,true),(703,true),(711,true)]
theorem inp_11476 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11476 := by
  exact input_gate (closedGate5 18 26) (closed_mem 18 26) cl_11476 (by decide) v h
def cl_11565 : CNF.NClause := [(723,true),(724,true),(725,false),(726,true),(727,true),(743,true)]
theorem inp_11565 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11565 := by
  exact input_gate (closedGate5 19 10) (closed_mem 19 10) cl_11565 (by decide) v h
def cl_11568 : CNF.NClause := [(717,true),(720,true),(723,true),(731,true),(734,true),(741,false)]
theorem inp_11568 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11568 := by
  exact input_gate (closedGate5 19 11) (closed_mem 19 11) cl_11568 (by decide) v h
def cl_11581 : CNF.NClause := [(716,true),(722,true),(723,true),(729,true),(735,false),(739,true)]
theorem inp_11581 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11581 := by
  exact input_gate (closedGate5 19 13) (closed_mem 19 13) cl_11581 (by decide) v h
def cl_11588 : CNF.NClause := [(714,true),(721,true),(723,true),(730,false),(737,true),(740,true)]
theorem inp_11588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11588 := by
  exact input_gate (closedGate5 19 14) (closed_mem 19 14) cl_11588 (by decide) v h
def cl_11600 : CNF.NClause := [(717,true),(719,true),(726,true),(728,false),(735,true),(740,true)]
theorem inp_11600 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11600 := by
  exact input_gate (closedGate5 19 16) (closed_mem 19 16) cl_11600 (by decide) v h
end Percolation.Replay
