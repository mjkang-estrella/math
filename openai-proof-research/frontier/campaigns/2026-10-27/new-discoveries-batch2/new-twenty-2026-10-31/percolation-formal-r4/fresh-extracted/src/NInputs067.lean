import NInputs066
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4044 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,false),(92,true)]
theorem inp_4044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4044 (by decide) v hb
def cl_4046 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,false),(92,true)]
theorem inp_4046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4046 (by decide) v hb
def cl_4048 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,false),(92,true)]
theorem inp_4048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4048 (by decide) v hb
def cl_4050 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,false),(92,true)]
theorem inp_4050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4050 (by decide) v hb
def cl_4052 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,false),(92,true)]
theorem inp_4052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4052 (by decide) v hb
def cl_4054 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,false),(92,true)]
theorem inp_4054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4054 (by decide) v hb
def cl_4056 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,false),(92,true)]
theorem inp_4056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4056 (by decide) v hb
def cl_4058 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,false),(92,true)]
theorem inp_4058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4058 (by decide) v hb
def cl_4060 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,false),(92,true)]
theorem inp_4060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4060 (by decide) v hb
def cl_4062 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,false),(92,true)]
theorem inp_4062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4062 (by decide) v hb
def cl_4064 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,false),(92,true)]
theorem inp_4064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4064 (by decide) v hb
def cl_4066 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,true),(92,true)]
theorem inp_4066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4066 (by decide) v hb
def cl_4068 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,true),(92,true)]
theorem inp_4068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4068 (by decide) v hb
def cl_4070 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,true),(92,true)]
theorem inp_4070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4070 (by decide) v hb
def cl_4072 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,true),(92,true)]
theorem inp_4072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4072 (by decide) v hb
def cl_4074 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,true),(92,true)]
theorem inp_4074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4074 (by decide) v hb
def cl_4076 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,true),(92,true)]
theorem inp_4076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4076 (by decide) v hb
def cl_4078 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,true),(92,true)]
theorem inp_4078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4078 (by decide) v hb
def cl_4080 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,true),(92,true)]
theorem inp_4080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4080 (by decide) v hb
def cl_4082 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,true),(92,true)]
theorem inp_4082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4082 (by decide) v hb
def cl_4084 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,true),(92,true)]
theorem inp_4084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4084 (by decide) v hb
def cl_4086 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,true),(92,true)]
theorem inp_4086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4086 (by decide) v hb
def cl_4088 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,true),(92,true)]
theorem inp_4088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4088 (by decide) v hb
def cl_4090 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,true),(92,true)]
theorem inp_4090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4090 (by decide) v hb
def cl_4092 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,true),(92,true)]
theorem inp_4092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4092 (by decide) v hb
def cl_4094 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,true),(92,true)]
theorem inp_4094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4094 (by decide) v hb
def cl_4096 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,true),(92,true)]
theorem inp_4096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4096 (by decide) v hb
def cl_4097 : CNF.NClause := [(32,true),(1,false),(66,false),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4097 v hb
def cl_4098 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4098 v hb
def cl_4099 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4099 (by decide) v hb
def cl_4100 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4100 (by decide) v hb
def cl_4101 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4101 (by decide) v hb
def cl_4102 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4102 (by decide) v hb
def cl_4103 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4103 (by decide) v hb
def cl_4104 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4104 (by decide) v hb
def cl_4105 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4105 v hb
def cl_4106 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4106 v hb
def cl_4107 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4107 (by decide) v hb
def cl_4108 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4108 (by decide) v hb
def cl_4109 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4109 (by decide) v hb
def cl_4110 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4110 (by decide) v hb
def cl_4111 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4111 (by decide) v hb
def cl_4112 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4112 (by decide) v hb
def cl_4113 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4113 (by decide) v hb
def cl_4114 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4114 (by decide) v hb
def cl_4115 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4115 (by decide) v hb
def cl_4116 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4116 (by decide) v hb
def cl_4117 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4117 (by decide) v hb
def cl_4118 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4118 (by decide) v hb
def cl_4119 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4119 (by decide) v hb
end Percolation.NReplay
