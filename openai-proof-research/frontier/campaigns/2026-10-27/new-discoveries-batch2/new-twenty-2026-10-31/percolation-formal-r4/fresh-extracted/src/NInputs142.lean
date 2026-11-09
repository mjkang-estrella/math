import NInputs141
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8078 : CNF.NClause := [(127,true),(131,true),(135,true),(139,false),(148,true),(153,true)]
theorem inp_8078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) cl_8078 (by decide) v hb
def cl_8079 : CNF.NClause := [(127,true),(131,true),(135,false),(139,true),(148,true),(153,true)]
theorem inp_8079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) cl_8079 (by decide) v hb
def cl_8080 : CNF.NClause := [(127,true),(131,false),(135,true),(139,true),(148,true),(153,true)]
theorem inp_8080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) cl_8080 (by decide) v hb
def cl_8081 : CNF.NClause := [(127,false),(131,true),(135,true),(139,true),(148,true),(153,true)]
theorem inp_8081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) cl_8081 (by decide) v hb
def cl_8082 : CNF.NClause := [(125,true),(133,true),(136,true),(139,true),(147,true),(152,false)]
theorem inp_8082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) cl_8082 (by decide) v hb
def cl_8083 : CNF.NClause := [(125,true),(133,true),(136,true),(139,true),(147,false),(152,true)]
theorem inp_8083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) cl_8083 (by decide) v hb
def cl_8084 : CNF.NClause := [(125,true),(133,true),(136,true),(139,false),(147,true),(152,true)]
theorem inp_8084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) cl_8084 (by decide) v hb
def cl_8085 : CNF.NClause := [(125,true),(133,true),(136,false),(139,true),(147,true),(152,true)]
theorem inp_8085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) cl_8085 (by decide) v hb
def cl_8086 : CNF.NClause := [(125,true),(133,false),(136,true),(139,true),(147,true),(152,true)]
theorem inp_8086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) cl_8086 (by decide) v hb
def cl_8087 : CNF.NClause := [(125,false),(133,true),(136,true),(139,true),(147,true),(152,true)]
theorem inp_8087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 19) (closed_mem 0 19) cl_8087 (by decide) v hb
def cl_8089 : CNF.NClause := [(129,true),(130,true),(131,true),(132,true),(133,false),(154,true)]
theorem inp_8089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) cl_8089 (by decide) v hb
def cl_8090 : CNF.NClause := [(129,true),(130,true),(131,true),(132,false),(133,true),(154,true)]
theorem inp_8090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) cl_8090 (by decide) v hb
def cl_8091 : CNF.NClause := [(129,true),(130,true),(131,false),(132,true),(133,true),(154,true)]
theorem inp_8091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) cl_8091 (by decide) v hb
def cl_8092 : CNF.NClause := [(129,true),(130,false),(131,true),(132,true),(133,true),(154,true)]
theorem inp_8092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) cl_8092 (by decide) v hb
def cl_8093 : CNF.NClause := [(129,false),(130,true),(131,true),(132,true),(133,true),(154,true)]
theorem inp_8093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) cl_8093 (by decide) v hb
def cl_8094 : CNF.NClause := [(128,true),(129,true),(135,true),(141,true),(147,true),(150,false)]
theorem inp_8094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8094 v hb
def cl_8095 : CNF.NClause := [(128,true),(129,true),(135,true),(141,true),(147,false),(150,true)]
theorem inp_8095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) cl_8095 (by decide) v hb
def cl_8096 : CNF.NClause := [(128,true),(129,true),(135,true),(141,false),(147,true),(150,true)]
theorem inp_8096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) cl_8096 (by decide) v hb
def cl_8097 : CNF.NClause := [(128,true),(129,true),(135,false),(141,true),(147,true),(150,true)]
theorem inp_8097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) cl_8097 (by decide) v hb
def cl_8098 : CNF.NClause := [(128,true),(129,false),(135,true),(141,true),(147,true),(150,true)]
theorem inp_8098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) cl_8098 (by decide) v hb
def cl_8099 : CNF.NClause := [(128,false),(129,true),(135,true),(141,true),(147,true),(150,true)]
theorem inp_8099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) cl_8099 (by decide) v hb
def cl_8100 : CNF.NClause := [(126,true),(129,true),(137,true),(140,true),(148,true),(152,false)]
theorem inp_8100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) cl_8100 (by decide) v hb
def cl_8101 : CNF.NClause := [(126,true),(129,true),(137,true),(140,true),(148,false),(152,true)]
theorem inp_8101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) cl_8101 (by decide) v hb
def cl_8102 : CNF.NClause := [(126,true),(129,true),(137,true),(140,false),(148,true),(152,true)]
theorem inp_8102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) cl_8102 (by decide) v hb
def cl_8103 : CNF.NClause := [(126,true),(129,true),(137,false),(140,true),(148,true),(152,true)]
theorem inp_8103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) cl_8103 (by decide) v hb
def cl_8104 : CNF.NClause := [(126,true),(129,false),(137,true),(140,true),(148,true),(152,true)]
theorem inp_8104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) cl_8104 (by decide) v hb
def cl_8105 : CNF.NClause := [(126,false),(129,true),(137,true),(140,true),(148,true),(152,true)]
theorem inp_8105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) cl_8105 (by decide) v hb
def cl_8106 : CNF.NClause := [(127,true),(129,true),(136,true),(143,true),(145,true),(151,false)]
theorem inp_8106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) cl_8106 (by decide) v hb
def cl_8107 : CNF.NClause := [(127,true),(129,true),(136,true),(143,true),(145,false),(151,true)]
theorem inp_8107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) cl_8107 (by decide) v hb
def cl_8108 : CNF.NClause := [(127,true),(129,true),(136,true),(143,false),(145,true),(151,true)]
theorem inp_8108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) cl_8108 (by decide) v hb
def cl_8109 : CNF.NClause := [(127,true),(129,true),(136,false),(143,true),(145,true),(151,true)]
theorem inp_8109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) cl_8109 (by decide) v hb
def cl_8110 : CNF.NClause := [(127,true),(129,false),(136,true),(143,true),(145,true),(151,true)]
theorem inp_8110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) cl_8110 (by decide) v hb
def cl_8111 : CNF.NClause := [(127,false),(129,true),(136,true),(143,true),(145,true),(151,true)]
theorem inp_8111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) cl_8111 (by decide) v hb
def cl_8112 : CNF.NClause := [(125,true),(129,true),(138,true),(142,true),(146,true),(153,false)]
theorem inp_8112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) cl_8112 (by decide) v hb
def cl_8113 : CNF.NClause := [(125,true),(129,true),(138,true),(142,true),(146,false),(153,true)]
theorem inp_8113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) cl_8113 (by decide) v hb
def cl_8114 : CNF.NClause := [(125,true),(129,true),(138,true),(142,false),(146,true),(153,true)]
theorem inp_8114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) cl_8114 (by decide) v hb
def cl_8115 : CNF.NClause := [(125,true),(129,true),(138,false),(142,true),(146,true),(153,true)]
theorem inp_8115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) cl_8115 (by decide) v hb
def cl_8116 : CNF.NClause := [(125,true),(129,false),(138,true),(142,true),(146,true),(153,true)]
theorem inp_8116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) cl_8116 (by decide) v hb
def cl_8117 : CNF.NClause := [(125,false),(129,true),(138,true),(142,true),(146,true),(153,true)]
theorem inp_8117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 24) (closed_mem 0 24) cl_8117 (by decide) v hb
def cl_8123 : CNF.NClause := [(124,false),(125,true),(126,true),(127,true),(128,true),(154,true)]
theorem inp_8123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 25) (closed_mem 0 25) cl_8123 (by decide) v hb
def cl_8129 : CNF.NClause := [(124,false),(133,true),(137,true),(141,true),(145,true),(153,true)]
theorem inp_8129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 26) (closed_mem 0 26) cl_8129 (by decide) v hb
def cl_8135 : CNF.NClause := [(124,false),(131,true),(138,true),(140,true),(147,true),(151,true)]
theorem inp_8135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 27) (closed_mem 0 27) cl_8135 (by decide) v hb
def cl_8141 : CNF.NClause := [(124,false),(132,true),(135,true),(143,true),(146,true),(152,true)]
theorem inp_8141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 28) (closed_mem 0 28) cl_8141 (by decide) v hb
def cl_8147 : CNF.NClause := [(124,false),(130,true),(136,true),(142,true),(148,true),(150,true)]
theorem inp_8147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8147 v hb
def cl_8153 : CNF.NClause := [(124,false),(129,true),(134,true),(139,true),(144,true),(149,true)]
theorem inp_8153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 30) (closed_mem 0 30) cl_8153 (by decide) v hb
def cl_8155 : CNF.NClause := [(180,true),(181,true),(182,true),(183,true),(184,false),(185,true)]
theorem inp_8155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) cl_8155 (by decide) v hb
def cl_8156 : CNF.NClause := [(180,true),(181,true),(182,true),(183,false),(184,true),(185,true)]
theorem inp_8156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) cl_8156 (by decide) v hb
def cl_8157 : CNF.NClause := [(180,true),(181,true),(182,false),(183,true),(184,true),(185,true)]
theorem inp_8157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) cl_8157 (by decide) v hb
def cl_8158 : CNF.NClause := [(180,true),(181,false),(182,true),(183,true),(184,true),(185,true)]
theorem inp_8158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) cl_8158 (by decide) v hb
def cl_8161 : CNF.NClause := [(159,true),(164,true),(169,true),(174,true),(179,false),(180,true)]
theorem inp_8161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) cl_8161 (by decide) v hb
end Percolation.NReplay
