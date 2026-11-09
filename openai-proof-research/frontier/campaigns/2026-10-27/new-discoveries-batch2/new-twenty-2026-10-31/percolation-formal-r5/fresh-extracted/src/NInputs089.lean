import NInputs088
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5197 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5197 (by decide) v hb
def cl_5198 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5198 (by decide) v hb
def cl_5199 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5199 (by decide) v hb
def cl_5200 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5200 (by decide) v hb
def cl_5201 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5201 (by decide) v hb
def cl_5202 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5202 (by decide) v hb
def cl_5203 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5203 (by decide) v hb
def cl_5204 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5204 (by decide) v hb
def cl_5205 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5205 (by decide) v hb
def cl_5206 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5206 (by decide) v hb
def cl_5207 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5207 (by decide) v hb
def cl_5208 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inp_5208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5208 (by decide) v hb
def cl_5209 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5209 (by decide) v hb
def cl_5210 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5210 (by decide) v hb
def cl_5211 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5211 (by decide) v hb
def cl_5212 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5212 (by decide) v hb
def cl_5213 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5213 (by decide) v hb
def cl_5214 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5214 (by decide) v hb
def cl_5215 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5215 (by decide) v hb
def cl_5216 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inp_5216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5216 (by decide) v hb
def cl_5217 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5217 (by decide) v hb
def cl_5218 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5218 v hb
def cl_5219 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5219 (by decide) v hb
def cl_5220 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5220 (by decide) v hb
def cl_5221 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5221 (by decide) v hb
def cl_5222 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5222 (by decide) v hb
def cl_5223 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5223 (by decide) v hb
def cl_5224 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5224 (by decide) v hb
def cl_5225 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5225 (by decide) v hb
def cl_5226 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5226 v hb
def cl_5227 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5227 (by decide) v hb
def cl_5228 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5228 (by decide) v hb
def cl_5229 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5229 (by decide) v hb
def cl_5230 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5230 (by decide) v hb
def cl_5231 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5231 (by decide) v hb
def cl_5232 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5232 (by decide) v hb
def cl_5233 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,true),(88,true)]
theorem inp_5233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5233 (by decide) v hb
def cl_5234 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,true),(88,true)]
theorem inp_5234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5234 (by decide) v hb
def cl_5236 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,true),(88,true)]
theorem inp_5236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5236 (by decide) v hb
def cl_5237 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,true),(88,true)]
theorem inp_5237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5237 (by decide) v hb
def cl_5238 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,true),(88,true)]
theorem inp_5238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5238 (by decide) v hb
def cl_5240 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,true),(88,true)]
theorem inp_5240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5240 (by decide) v hb
def cl_5242 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,true),(88,true)]
theorem inp_5242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5242 (by decide) v hb
def cl_5244 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,true),(88,true)]
theorem inp_5244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5244 (by decide) v hb
def cl_5245 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,true),(88,true)]
theorem inp_5245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5245 (by decide) v hb
def cl_5246 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,true),(88,true)]
theorem inp_5246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5246 (by decide) v hb
def cl_5248 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,true),(88,true)]
theorem inp_5248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5248 (by decide) v hb
def cl_5249 : CNF.NClause := [(41,true),(10,false),(72,false),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5249 (by decide) v hb
def cl_5250 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5250 (by decide) v hb
def cl_5251 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inp_5251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5251 (by decide) v hb
end Percolation.NReplay
