import NInputs068
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4174 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4174 (by decide) v hb
def cl_4175 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4175 (by decide) v hb
def cl_4176 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4176 (by decide) v hb
def cl_4177 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4177 (by decide) v hb
def cl_4178 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4178 (by decide) v hb
def cl_4179 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4179 (by decide) v hb
def cl_4180 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4180 (by decide) v hb
def cl_4181 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4181 (by decide) v hb
def cl_4182 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4182 (by decide) v hb
def cl_4183 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4183 (by decide) v hb
def cl_4184 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inp_4184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4184 (by decide) v hb
def cl_4185 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4185 (by decide) v hb
def cl_4186 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4186 (by decide) v hb
def cl_4187 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4187 (by decide) v hb
def cl_4188 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4188 (by decide) v hb
def cl_4189 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4189 (by decide) v hb
def cl_4190 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4190 (by decide) v hb
def cl_4191 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4191 (by decide) v hb
def cl_4192 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inp_4192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4192 (by decide) v hb
def cl_4193 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4193 (by decide) v hb
def cl_4194 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4194 (by decide) v hb
def cl_4195 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4195 (by decide) v hb
def cl_4196 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4196 (by decide) v hb
def cl_4197 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4197 (by decide) v hb
def cl_4198 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4198 (by decide) v hb
def cl_4199 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4199 (by decide) v hb
def cl_4200 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inp_4200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4200 (by decide) v hb
def cl_4201 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4201 (by decide) v hb
def cl_4202 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4202 (by decide) v hb
def cl_4203 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4203 (by decide) v hb
def cl_4204 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4204 (by decide) v hb
def cl_4205 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4205 (by decide) v hb
def cl_4206 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4206 (by decide) v hb
def cl_4207 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4207 (by decide) v hb
def cl_4208 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inp_4208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4208 (by decide) v hb
def cl_4209 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4209 (by decide) v hb
def cl_4210 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4210 (by decide) v hb
def cl_4211 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4211 (by decide) v hb
def cl_4212 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4212 (by decide) v hb
def cl_4213 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4213 (by decide) v hb
def cl_4214 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4214 (by decide) v hb
def cl_4215 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4215 (by decide) v hb
def cl_4216 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inp_4216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4216 (by decide) v hb
def cl_4217 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,true),(87,true)]
theorem inp_4217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4217 (by decide) v hb
def cl_4218 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,true),(87,true)]
theorem inp_4218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4218 (by decide) v hb
def cl_4221 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inp_4221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4221 (by decide) v hb
def cl_4222 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inp_4222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4222 (by decide) v hb
def cl_4223 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inp_4223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4223 (by decide) v hb
def cl_4224 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inp_4224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4224 (by decide) v hb
def cl_4225 : CNF.NClause := [(33,true),(2,false),(64,false),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4225 (by decide) v hb
end Percolation.NReplay
