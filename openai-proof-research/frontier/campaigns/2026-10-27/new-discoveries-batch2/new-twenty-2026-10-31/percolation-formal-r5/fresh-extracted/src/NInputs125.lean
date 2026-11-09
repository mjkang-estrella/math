import NInputs124
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7065 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7065 (by decide) v hb
def cl_7066 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7066 (by decide) v hb
def cl_7067 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7067 (by decide) v hb
def cl_7068 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7068 (by decide) v hb
def cl_7069 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7069 (by decide) v hb
def cl_7070 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7070 (by decide) v hb
def cl_7071 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7071 (by decide) v hb
def cl_7072 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inp_7072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7072 (by decide) v hb
def cl_7073 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7073 (by decide) v hb
def cl_7074 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7074 (by decide) v hb
def cl_7075 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7075 (by decide) v hb
def cl_7076 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7076 (by decide) v hb
def cl_7077 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7077 (by decide) v hb
def cl_7078 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7078 (by decide) v hb
def cl_7079 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7079 (by decide) v hb
def cl_7080 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inp_7080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7080 (by decide) v hb
def cl_7081 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7081 (by decide) v hb
def cl_7082 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7082 (by decide) v hb
def cl_7083 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7083 (by decide) v hb
def cl_7084 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7084 (by decide) v hb
def cl_7085 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7085 (by decide) v hb
def cl_7086 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7086 (by decide) v hb
def cl_7087 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7087 (by decide) v hb
def cl_7088 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inp_7088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7088 (by decide) v hb
def cl_7089 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7089 (by decide) v hb
def cl_7090 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7090 (by decide) v hb
def cl_7091 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7091 (by decide) v hb
def cl_7092 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7092 (by decide) v hb
def cl_7093 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7093 (by decide) v hb
def cl_7094 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7094 (by decide) v hb
def cl_7095 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7095 (by decide) v hb
def cl_7096 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inp_7096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7096 (by decide) v hb
def cl_7097 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7097 (by decide) v hb
def cl_7098 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7098 (by decide) v hb
def cl_7099 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7099 (by decide) v hb
def cl_7100 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7100 (by decide) v hb
def cl_7101 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7101 (by decide) v hb
def cl_7102 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7102 (by decide) v hb
def cl_7103 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7103 (by decide) v hb
def cl_7104 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inp_7104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7104 (by decide) v hb
def cl_7105 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7105 (by decide) v hb
def cl_7106 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7106 (by decide) v hb
def cl_7107 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7107 (by decide) v hb
def cl_7108 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7108 (by decide) v hb
def cl_7109 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7109 (by decide) v hb
def cl_7110 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7110 (by decide) v hb
def cl_7111 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7111 (by decide) v hb
def cl_7112 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inp_7112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7112 (by decide) v hb
def cl_7113 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7113 (by decide) v hb
def cl_7114 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7114 (by decide) v hb
end Percolation.NReplay
