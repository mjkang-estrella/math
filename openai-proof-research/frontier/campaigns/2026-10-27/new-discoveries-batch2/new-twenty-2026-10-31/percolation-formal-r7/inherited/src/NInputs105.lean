import NInputs104
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6024 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6024 (by decide) v hb
def cl_6025 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6025 (by decide) v hb
def cl_6026 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6026 v hb
def cl_6027 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6027 (by decide) v hb
def cl_6028 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6028 (by decide) v hb
def cl_6029 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6029 (by decide) v hb
def cl_6030 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6030 (by decide) v hb
def cl_6031 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6031 (by decide) v hb
def cl_6032 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6032 (by decide) v hb
def cl_6033 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6033 (by decide) v hb
def cl_6034 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6034 (by decide) v hb
def cl_6035 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6035 (by decide) v hb
def cl_6036 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6036 (by decide) v hb
def cl_6037 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6037 (by decide) v hb
def cl_6038 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6038 (by decide) v hb
def cl_6039 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6039 (by decide) v hb
def cl_6040 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inp_6040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6040 (by decide) v hb
def cl_6041 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6041 (by decide) v hb
def cl_6042 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6042 v hb
def cl_6043 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6043 (by decide) v hb
def cl_6044 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6044 (by decide) v hb
def cl_6045 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6045 (by decide) v hb
def cl_6046 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6046 (by decide) v hb
def cl_6047 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6047 (by decide) v hb
def cl_6048 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6048 (by decide) v hb
def cl_6049 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6049 (by decide) v hb
def cl_6050 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6050 (by decide) v hb
def cl_6051 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6051 (by decide) v hb
def cl_6052 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6052 (by decide) v hb
def cl_6053 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6053 (by decide) v hb
def cl_6054 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6054 (by decide) v hb
def cl_6055 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6055 (by decide) v hb
def cl_6056 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inp_6056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6056 (by decide) v hb
def cl_6057 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6057 (by decide) v hb
def cl_6058 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6058 v hb
def cl_6059 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6059 (by decide) v hb
def cl_6060 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6060 (by decide) v hb
def cl_6061 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6061 (by decide) v hb
def cl_6062 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6062 (by decide) v hb
def cl_6063 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6063 (by decide) v hb
def cl_6064 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6064 (by decide) v hb
def cl_6065 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6065 (by decide) v hb
def cl_6066 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6066 (by decide) v hb
def cl_6067 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6067 (by decide) v hb
def cl_6068 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6068 (by decide) v hb
def cl_6069 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6069 (by decide) v hb
def cl_6070 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6070 (by decide) v hb
def cl_6071 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6071 (by decide) v hb
def cl_6072 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inp_6072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6072 (by decide) v hb
def cl_6073 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6073 (by decide) v hb
end Percolation.NReplay
