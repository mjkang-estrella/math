import NInputs186
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12042 : CNF.NClause := [(775,true),(783,true),(786,true),(794,true),(797,true),(803,false)]
theorem inp_12042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 28) (closed_mem 21 28) cl_12042 (by decide) v hb
def cl_12043 : CNF.NClause := [(775,true),(783,true),(786,true),(794,true),(797,false),(803,true)]
theorem inp_12043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 28) (closed_mem 21 28) cl_12043 (by decide) v hb
def cl_12044 : CNF.NClause := [(775,true),(783,true),(786,true),(794,false),(797,true),(803,true)]
theorem inp_12044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 28) (closed_mem 21 28) cl_12044 (by decide) v hb
def cl_12045 : CNF.NClause := [(775,true),(783,true),(786,false),(794,true),(797,true),(803,true)]
theorem inp_12045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 28) (closed_mem 21 28) cl_12045 (by decide) v hb
def cl_12046 : CNF.NClause := [(775,true),(783,false),(786,true),(794,true),(797,true),(803,true)]
theorem inp_12046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_12046 v hb
def cl_12048 : CNF.NClause := [(775,true),(781,true),(787,true),(793,true),(799,true),(801,false)]
theorem inp_12048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 29) (closed_mem 21 29) cl_12048 (by decide) v hb
def cl_12049 : CNF.NClause := [(775,true),(781,true),(787,true),(793,true),(799,false),(801,true)]
theorem inp_12049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 29) (closed_mem 21 29) cl_12049 (by decide) v hb
def cl_12050 : CNF.NClause := [(775,true),(781,true),(787,true),(793,false),(799,true),(801,true)]
theorem inp_12050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 29) (closed_mem 21 29) cl_12050 (by decide) v hb
def cl_12051 : CNF.NClause := [(775,true),(781,true),(787,false),(793,true),(799,true),(801,true)]
theorem inp_12051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 29) (closed_mem 21 29) cl_12051 (by decide) v hb
def cl_12052 : CNF.NClause := [(775,true),(781,false),(787,true),(793,true),(799,true),(801,true)]
theorem inp_12052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 29) (closed_mem 21 29) cl_12052 (by decide) v hb
def cl_12055 : CNF.NClause := [(775,true),(780,true),(785,true),(790,true),(795,false),(800,true)]
theorem inp_12055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 30) (closed_mem 21 30) cl_12055 (by decide) v hb
def cl_12056 : CNF.NClause := [(775,true),(780,true),(785,true),(790,false),(795,true),(800,true)]
theorem inp_12056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 30) (closed_mem 21 30) cl_12056 (by decide) v hb
def cl_12057 : CNF.NClause := [(775,true),(780,true),(785,false),(790,true),(795,true),(800,true)]
theorem inp_12057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 30) (closed_mem 21 30) cl_12057 (by decide) v hb
def cl_12058 : CNF.NClause := [(775,true),(780,false),(785,true),(790,true),(795,true),(800,true)]
theorem inp_12058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 30) (closed_mem 21 30) cl_12058 (by decide) v hb
def cl_12061 : CNF.NClause := [(831,true),(832,true),(833,true),(834,true),(835,false),(836,true)]
theorem inp_12061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 0) (closed_mem 22 0) cl_12061 (by decide) v hb
def cl_12062 : CNF.NClause := [(831,true),(832,true),(833,true),(834,false),(835,true),(836,true)]
theorem inp_12062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 0) (closed_mem 22 0) cl_12062 (by decide) v hb
def cl_12063 : CNF.NClause := [(831,true),(832,true),(833,false),(834,true),(835,true),(836,true)]
theorem inp_12063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 0) (closed_mem 22 0) cl_12063 (by decide) v hb
def cl_12064 : CNF.NClause := [(831,true),(832,false),(833,true),(834,true),(835,true),(836,true)]
theorem inp_12064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 0) (closed_mem 22 0) cl_12064 (by decide) v hb
def cl_12067 : CNF.NClause := [(810,true),(815,true),(820,true),(825,true),(830,false),(831,true)]
theorem inp_12067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 1) (closed_mem 22 1) cl_12067 (by decide) v hb
def cl_12068 : CNF.NClause := [(810,true),(815,true),(820,true),(825,false),(830,true),(831,true)]
theorem inp_12068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 1) (closed_mem 22 1) cl_12068 (by decide) v hb
def cl_12069 : CNF.NClause := [(810,true),(815,true),(820,false),(825,true),(830,true),(831,true)]
theorem inp_12069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 1) (closed_mem 22 1) cl_12069 (by decide) v hb
def cl_12070 : CNF.NClause := [(810,true),(815,false),(820,true),(825,true),(830,true),(831,true)]
theorem inp_12070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 1) (closed_mem 22 1) cl_12070 (by decide) v hb
def cl_12071 : CNF.NClause := [(810,false),(815,true),(820,true),(825,true),(830,true),(831,true)]
theorem inp_12071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 1) (closed_mem 22 1) cl_12071 (by decide) v hb
def cl_12073 : CNF.NClause := [(808,true),(813,true),(818,true),(823,true),(828,false),(831,true)]
theorem inp_12073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 2) (closed_mem 22 2) cl_12073 (by decide) v hb
def cl_12079 : CNF.NClause := [(809,true),(814,true),(819,true),(824,true),(829,false),(831,true)]
theorem inp_12079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 3) (closed_mem 22 3) cl_12079 (by decide) v hb
def cl_12080 : CNF.NClause := [(809,true),(814,true),(819,true),(824,false),(829,true),(831,true)]
theorem inp_12080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 3) (closed_mem 22 3) cl_12080 (by decide) v hb
def cl_12081 : CNF.NClause := [(809,true),(814,true),(819,false),(824,true),(829,true),(831,true)]
theorem inp_12081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 3) (closed_mem 22 3) cl_12081 (by decide) v hb
def cl_12082 : CNF.NClause := [(809,true),(814,false),(819,true),(824,true),(829,true),(831,true)]
theorem inp_12082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 3) (closed_mem 22 3) cl_12082 (by decide) v hb
def cl_12083 : CNF.NClause := [(809,false),(814,true),(819,true),(824,true),(829,true),(831,true)]
theorem inp_12083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 3) (closed_mem 22 3) cl_12083 (by decide) v hb
def cl_12085 : CNF.NClause := [(807,true),(812,true),(817,true),(822,true),(827,false),(831,true)]
theorem inp_12085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 4) (closed_mem 22 4) cl_12085 (by decide) v hb
def cl_12086 : CNF.NClause := [(807,true),(812,true),(817,true),(822,false),(827,true),(831,true)]
theorem inp_12086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 4) (closed_mem 22 4) cl_12086 (by decide) v hb
def cl_12087 : CNF.NClause := [(807,true),(812,true),(817,false),(822,true),(827,true),(831,true)]
theorem inp_12087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 4) (closed_mem 22 4) cl_12087 (by decide) v hb
def cl_12088 : CNF.NClause := [(807,true),(812,false),(817,true),(822,true),(827,true),(831,true)]
theorem inp_12088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 4) (closed_mem 22 4) cl_12088 (by decide) v hb
def cl_12089 : CNF.NClause := [(807,false),(812,true),(817,true),(822,true),(827,true),(831,true)]
theorem inp_12089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 4) (closed_mem 22 4) cl_12089 (by decide) v hb
def cl_12093 : CNF.NClause := [(826,true),(827,true),(828,false),(829,true),(830,true),(836,true)]
theorem inp_12093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_12093 v hb
def cl_12096 : CNF.NClause := [(810,true),(814,true),(818,true),(822,true),(826,true),(835,false)]
theorem inp_12096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 6) (closed_mem 22 6) cl_12096 (by decide) v hb
def cl_12099 : CNF.NClause := [(810,true),(814,true),(818,false),(822,true),(826,true),(835,true)]
theorem inp_12099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 6) (closed_mem 22 6) cl_12099 (by decide) v hb
def cl_12100 : CNF.NClause := [(810,true),(814,false),(818,true),(822,true),(826,true),(835,true)]
theorem inp_12100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 6) (closed_mem 22 6) cl_12100 (by decide) v hb
def cl_12101 : CNF.NClause := [(810,false),(814,true),(818,true),(822,true),(826,true),(835,true)]
theorem inp_12101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 6) (closed_mem 22 6) cl_12101 (by decide) v hb
def cl_12103 : CNF.NClause := [(808,true),(815,true),(817,true),(824,true),(826,false),(833,true)]
theorem inp_12103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 7) (closed_mem 22 7) cl_12103 (by decide) v hb
def cl_12107 : CNF.NClause := [(808,false),(815,true),(817,true),(824,true),(826,true),(833,true)]
theorem inp_12107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 7) (closed_mem 22 7) cl_12107 (by decide) v hb
def cl_12108 : CNF.NClause := [(809,true),(812,true),(820,true),(823,true),(826,true),(834,false)]
theorem inp_12108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 8) (closed_mem 22 8) cl_12108 (by decide) v hb
def cl_12109 : CNF.NClause := [(809,true),(812,true),(820,true),(823,true),(826,false),(834,true)]
theorem inp_12109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 8) (closed_mem 22 8) cl_12109 (by decide) v hb
def cl_12110 : CNF.NClause := [(809,true),(812,true),(820,true),(823,false),(826,true),(834,true)]
theorem inp_12110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 8) (closed_mem 22 8) cl_12110 (by decide) v hb
def cl_12113 : CNF.NClause := [(809,false),(812,true),(820,true),(823,true),(826,true),(834,true)]
theorem inp_12113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 8) (closed_mem 22 8) cl_12113 (by decide) v hb
def cl_12115 : CNF.NClause := [(807,true),(813,true),(819,true),(825,true),(826,false),(832,true)]
theorem inp_12115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 9) (closed_mem 22 9) cl_12115 (by decide) v hb
def cl_12116 : CNF.NClause := [(807,true),(813,true),(819,true),(825,false),(826,true),(832,true)]
theorem inp_12116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 9) (closed_mem 22 9) cl_12116 (by decide) v hb
def cl_12117 : CNF.NClause := [(807,true),(813,true),(819,false),(825,true),(826,true),(832,true)]
theorem inp_12117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 9) (closed_mem 22 9) cl_12117 (by decide) v hb
def cl_12119 : CNF.NClause := [(807,false),(813,true),(819,true),(825,true),(826,true),(832,true)]
theorem inp_12119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 9) (closed_mem 22 9) cl_12119 (by decide) v hb
def cl_12121 : CNF.NClause := [(816,true),(817,true),(818,true),(819,true),(820,false),(836,true)]
theorem inp_12121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 10) (closed_mem 22 10) cl_12121 (by decide) v hb
end Percolation.NReplay
