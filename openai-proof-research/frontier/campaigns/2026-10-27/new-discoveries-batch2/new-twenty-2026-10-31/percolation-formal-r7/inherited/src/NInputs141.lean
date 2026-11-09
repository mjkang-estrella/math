import NInputs140
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8026 : CNF.NClause := [(125,true),(131,false),(137,true),(143,true),(144,true),(150,true)]
theorem inp_8026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) cl_8026 (by decide) v hb
def cl_8027 : CNF.NClause := [(125,false),(131,true),(137,true),(143,true),(144,true),(150,true)]
theorem inp_8027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) cl_8027 (by decide) v hb
def cl_8029 : CNF.NClause := [(134,true),(135,true),(136,true),(137,true),(138,false),(154,true)]
theorem inp_8029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) cl_8029 (by decide) v hb
def cl_8030 : CNF.NClause := [(134,true),(135,true),(136,true),(137,false),(138,true),(154,true)]
theorem inp_8030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) cl_8030 (by decide) v hb
def cl_8031 : CNF.NClause := [(134,true),(135,true),(136,false),(137,true),(138,true),(154,true)]
theorem inp_8031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) cl_8031 (by decide) v hb
def cl_8032 : CNF.NClause := [(134,true),(135,false),(136,true),(137,true),(138,true),(154,true)]
theorem inp_8032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) cl_8032 (by decide) v hb
def cl_8033 : CNF.NClause := [(134,false),(135,true),(136,true),(137,true),(138,true),(154,true)]
theorem inp_8033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) cl_8033 (by decide) v hb
def cl_8034 : CNF.NClause := [(128,true),(131,true),(134,true),(142,true),(145,true),(152,false)]
theorem inp_8034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) cl_8034 (by decide) v hb
def cl_8035 : CNF.NClause := [(128,true),(131,true),(134,true),(142,true),(145,false),(152,true)]
theorem inp_8035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) cl_8035 (by decide) v hb
def cl_8036 : CNF.NClause := [(128,true),(131,true),(134,true),(142,false),(145,true),(152,true)]
theorem inp_8036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) cl_8036 (by decide) v hb
def cl_8037 : CNF.NClause := [(128,true),(131,true),(134,false),(142,true),(145,true),(152,true)]
theorem inp_8037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) cl_8037 (by decide) v hb
def cl_8038 : CNF.NClause := [(128,true),(131,false),(134,true),(142,true),(145,true),(152,true)]
theorem inp_8038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) cl_8038 (by decide) v hb
def cl_8039 : CNF.NClause := [(128,false),(131,true),(134,true),(142,true),(145,true),(152,true)]
theorem inp_8039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) cl_8039 (by decide) v hb
def cl_8040 : CNF.NClause := [(126,true),(130,true),(134,true),(143,true),(147,true),(153,false)]
theorem inp_8040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) cl_8040 (by decide) v hb
def cl_8041 : CNF.NClause := [(126,true),(130,true),(134,true),(143,true),(147,false),(153,true)]
theorem inp_8041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) cl_8041 (by decide) v hb
def cl_8042 : CNF.NClause := [(126,true),(130,true),(134,true),(143,false),(147,true),(153,true)]
theorem inp_8042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) cl_8042 (by decide) v hb
def cl_8043 : CNF.NClause := [(126,true),(130,true),(134,false),(143,true),(147,true),(153,true)]
theorem inp_8043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) cl_8043 (by decide) v hb
def cl_8044 : CNF.NClause := [(126,true),(130,false),(134,true),(143,true),(147,true),(153,true)]
theorem inp_8044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) cl_8044 (by decide) v hb
def cl_8045 : CNF.NClause := [(126,false),(130,true),(134,true),(143,true),(147,true),(153,true)]
theorem inp_8045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) cl_8045 (by decide) v hb
def cl_8046 : CNF.NClause := [(127,true),(133,true),(134,true),(140,true),(146,true),(150,false)]
theorem inp_8046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) cl_8046 (by decide) v hb
def cl_8047 : CNF.NClause := [(127,true),(133,true),(134,true),(140,true),(146,false),(150,true)]
theorem inp_8047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) cl_8047 (by decide) v hb
def cl_8048 : CNF.NClause := [(127,true),(133,true),(134,true),(140,false),(146,true),(150,true)]
theorem inp_8048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) cl_8048 (by decide) v hb
def cl_8049 : CNF.NClause := [(127,true),(133,true),(134,false),(140,true),(146,true),(150,true)]
theorem inp_8049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) cl_8049 (by decide) v hb
def cl_8050 : CNF.NClause := [(127,true),(133,false),(134,true),(140,true),(146,true),(150,true)]
theorem inp_8050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) cl_8050 (by decide) v hb
def cl_8051 : CNF.NClause := [(127,false),(133,true),(134,true),(140,true),(146,true),(150,true)]
theorem inp_8051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) cl_8051 (by decide) v hb
def cl_8052 : CNF.NClause := [(125,true),(132,true),(134,true),(141,true),(148,true),(151,false)]
theorem inp_8052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) cl_8052 (by decide) v hb
def cl_8053 : CNF.NClause := [(125,true),(132,true),(134,true),(141,true),(148,false),(151,true)]
theorem inp_8053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) cl_8053 (by decide) v hb
def cl_8054 : CNF.NClause := [(125,true),(132,true),(134,true),(141,false),(148,true),(151,true)]
theorem inp_8054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8054 v hb
def cl_8055 : CNF.NClause := [(125,true),(132,true),(134,false),(141,true),(148,true),(151,true)]
theorem inp_8055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) cl_8055 (by decide) v hb
def cl_8056 : CNF.NClause := [(125,true),(132,false),(134,true),(141,true),(148,true),(151,true)]
theorem inp_8056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) cl_8056 (by decide) v hb
def cl_8057 : CNF.NClause := [(125,false),(132,true),(134,true),(141,true),(148,true),(151,true)]
theorem inp_8057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) cl_8057 (by decide) v hb
def cl_8059 : CNF.NClause := [(139,true),(140,true),(141,true),(142,true),(143,false),(154,true)]
theorem inp_8059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) cl_8059 (by decide) v hb
def cl_8060 : CNF.NClause := [(139,true),(140,true),(141,true),(142,false),(143,true),(154,true)]
theorem inp_8060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) cl_8060 (by decide) v hb
def cl_8061 : CNF.NClause := [(139,true),(140,true),(141,false),(142,true),(143,true),(154,true)]
theorem inp_8061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) cl_8061 (by decide) v hb
def cl_8062 : CNF.NClause := [(139,true),(140,false),(141,true),(142,true),(143,true),(154,true)]
theorem inp_8062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) cl_8062 (by decide) v hb
def cl_8063 : CNF.NClause := [(139,false),(140,true),(141,true),(142,true),(143,true),(154,true)]
theorem inp_8063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) cl_8063 (by decide) v hb
def cl_8064 : CNF.NClause := [(128,true),(130,true),(137,true),(139,true),(146,true),(151,false)]
theorem inp_8064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) cl_8064 (by decide) v hb
def cl_8065 : CNF.NClause := [(128,true),(130,true),(137,true),(139,true),(146,false),(151,true)]
theorem inp_8065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) cl_8065 (by decide) v hb
def cl_8066 : CNF.NClause := [(128,true),(130,true),(137,true),(139,false),(146,true),(151,true)]
theorem inp_8066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) cl_8066 (by decide) v hb
def cl_8067 : CNF.NClause := [(128,true),(130,true),(137,false),(139,true),(146,true),(151,true)]
theorem inp_8067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) cl_8067 (by decide) v hb
def cl_8068 : CNF.NClause := [(128,true),(130,false),(137,true),(139,true),(146,true),(151,true)]
theorem inp_8068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) cl_8068 (by decide) v hb
def cl_8069 : CNF.NClause := [(128,false),(130,true),(137,true),(139,true),(146,true),(151,true)]
theorem inp_8069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) cl_8069 (by decide) v hb
def cl_8070 : CNF.NClause := [(126,true),(132,true),(138,true),(139,true),(145,true),(150,false)]
theorem inp_8070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) cl_8070 (by decide) v hb
def cl_8071 : CNF.NClause := [(126,true),(132,true),(138,true),(139,true),(145,false),(150,true)]
theorem inp_8071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) cl_8071 (by decide) v hb
def cl_8072 : CNF.NClause := [(126,true),(132,true),(138,true),(139,false),(145,true),(150,true)]
theorem inp_8072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) cl_8072 (by decide) v hb
def cl_8073 : CNF.NClause := [(126,true),(132,true),(138,false),(139,true),(145,true),(150,true)]
theorem inp_8073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) cl_8073 (by decide) v hb
def cl_8074 : CNF.NClause := [(126,true),(132,false),(138,true),(139,true),(145,true),(150,true)]
theorem inp_8074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) cl_8074 (by decide) v hb
def cl_8075 : CNF.NClause := [(126,false),(132,true),(138,true),(139,true),(145,true),(150,true)]
theorem inp_8075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) cl_8075 (by decide) v hb
def cl_8076 : CNF.NClause := [(127,true),(131,true),(135,true),(139,true),(148,true),(153,false)]
theorem inp_8076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) cl_8076 (by decide) v hb
def cl_8077 : CNF.NClause := [(127,true),(131,true),(135,true),(139,true),(148,false),(153,true)]
theorem inp_8077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) cl_8077 (by decide) v hb
end Percolation.NReplay
