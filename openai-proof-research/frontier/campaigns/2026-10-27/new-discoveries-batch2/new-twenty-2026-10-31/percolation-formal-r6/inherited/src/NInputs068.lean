import NInputs067
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4120 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inp_4120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4120 (by decide) v hb
def cl_4121 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,false),(87,false)]
theorem inp_4121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4121 (by decide) v hb
def cl_4122 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,false),(87,false)]
theorem inp_4122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4122 (by decide) v hb
def cl_4124 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,true),(86,false),(87,false)]
theorem inp_4124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4124 (by decide) v hb
def cl_4125 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inp_4125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4125 (by decide) v hb
def cl_4126 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inp_4126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4126 (by decide) v hb
def cl_4127 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inp_4127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4127 (by decide) v hb
def cl_4128 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inp_4128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4128 (by decide) v hb
def cl_4129 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4129 (by decide) v hb
def cl_4130 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4130 (by decide) v hb
def cl_4131 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4131 (by decide) v hb
def cl_4132 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4132 (by decide) v hb
def cl_4133 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4133 (by decide) v hb
def cl_4134 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4134 (by decide) v hb
def cl_4135 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4135 (by decide) v hb
def cl_4136 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inp_4136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4136 (by decide) v hb
def cl_4137 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4137 (by decide) v hb
def cl_4138 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4138 (by decide) v hb
def cl_4139 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4139 (by decide) v hb
def cl_4140 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4140 (by decide) v hb
def cl_4141 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4141 (by decide) v hb
def cl_4142 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4142 (by decide) v hb
def cl_4143 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4143 (by decide) v hb
def cl_4144 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inp_4144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4144 (by decide) v hb
def cl_4145 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inp_4145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4145 (by decide) v hb
def cl_4146 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inp_4146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4146 (by decide) v hb
def cl_4147 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inp_4147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4147 (by decide) v hb
def cl_4148 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inp_4148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4148 (by decide) v hb
def cl_4149 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,true),(87,false)]
theorem inp_4149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4149 (by decide) v hb
def cl_4150 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,true),(87,false)]
theorem inp_4150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4150 (by decide) v hb
def cl_4152 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,true),(87,false)]
theorem inp_4152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4152 (by decide) v hb
def cl_4153 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,true),(87,false)]
theorem inp_4153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4153 (by decide) v hb
def cl_4154 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,true),(87,false)]
theorem inp_4154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4154 (by decide) v hb
def cl_4157 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inp_4157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4157 (by decide) v hb
def cl_4158 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inp_4158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4158 (by decide) v hb
def cl_4159 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inp_4159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4159 (by decide) v hb
def cl_4160 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inp_4160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4160 (by decide) v hb
def cl_4161 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4161 (by decide) v hb
def cl_4162 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4162 v hb
def cl_4163 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4163 (by decide) v hb
def cl_4164 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4164 (by decide) v hb
def cl_4165 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4165 (by decide) v hb
def cl_4166 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4166 (by decide) v hb
def cl_4167 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4167 (by decide) v hb
def cl_4168 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4168 (by decide) v hb
def cl_4169 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4169 v hb
def cl_4170 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4170 v hb
def cl_4171 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4171 (by decide) v hb
def cl_4172 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4172 (by decide) v hb
def cl_4173 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4173 (by decide) v hb
end Percolation.NReplay
