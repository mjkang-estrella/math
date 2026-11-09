import NInputs105
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6074 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6074 v hb
def cl_6075 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6075 (by decide) v hb
def cl_6076 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6076 (by decide) v hb
def cl_6077 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6077 (by decide) v hb
def cl_6078 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6078 (by decide) v hb
def cl_6079 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6079 (by decide) v hb
def cl_6080 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6080 (by decide) v hb
def cl_6081 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6081 (by decide) v hb
def cl_6082 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6082 (by decide) v hb
def cl_6083 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6083 (by decide) v hb
def cl_6084 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6084 (by decide) v hb
def cl_6085 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6085 (by decide) v hb
def cl_6086 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6086 (by decide) v hb
def cl_6087 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6087 (by decide) v hb
def cl_6088 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inp_6088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6088 (by decide) v hb
def cl_6089 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6089 (by decide) v hb
def cl_6090 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6090 v hb
def cl_6091 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6091 (by decide) v hb
def cl_6092 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6092 (by decide) v hb
def cl_6093 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6093 (by decide) v hb
def cl_6094 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6094 v hb
def cl_6095 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6095 (by decide) v hb
def cl_6096 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6096 (by decide) v hb
def cl_6097 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inp_6097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6097 (by decide) v hb
def cl_6098 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inp_6098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6098 (by decide) v hb
def cl_6099 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inp_6099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6099 (by decide) v hb
def cl_6100 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,false),(89,true)]
theorem inp_6100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6100 (by decide) v hb
def cl_6101 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,false),(89,true)]
theorem inp_6101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6101 (by decide) v hb
def cl_6102 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,false),(89,true)]
theorem inp_6102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6102 (by decide) v hb
def cl_6104 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,false),(89,true)]
theorem inp_6104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6104 (by decide) v hb
def cl_6105 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6105 (by decide) v hb
def cl_6106 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6106 v hb
def cl_6107 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6107 (by decide) v hb
def cl_6108 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6108 (by decide) v hb
def cl_6109 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6109 (by decide) v hb
def cl_6110 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6110 (by decide) v hb
def cl_6111 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6111 (by decide) v hb
def cl_6112 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6112 (by decide) v hb
def cl_6113 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6113 (by decide) v hb
def cl_6114 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6114 (by decide) v hb
def cl_6115 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6115 (by decide) v hb
def cl_6116 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6116 (by decide) v hb
def cl_6117 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6117 (by decide) v hb
def cl_6118 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6118 (by decide) v hb
def cl_6119 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6119 (by decide) v hb
def cl_6120 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inp_6120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6120 (by decide) v hb
def cl_6121 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6121 (by decide) v hb
def cl_6122 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6122 v hb
def cl_6123 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6123 (by decide) v hb
def cl_6124 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6124 (by decide) v hb
end Percolation.NReplay
