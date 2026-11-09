import NInputs087
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5147 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5147 (by decide) v hb
def cl_5148 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5148 (by decide) v hb
def cl_5149 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5149 (by decide) v hb
def cl_5150 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5150 (by decide) v hb
def cl_5151 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5151 (by decide) v hb
def cl_5152 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5152 (by decide) v hb
def cl_5153 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5153 (by decide) v hb
def cl_5154 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5154 v hb
def cl_5155 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5155 (by decide) v hb
def cl_5156 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5156 (by decide) v hb
def cl_5157 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5157 (by decide) v hb
def cl_5158 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5158 (by decide) v hb
def cl_5159 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5159 (by decide) v hb
def cl_5160 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5160 (by decide) v hb
def cl_5161 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5161 (by decide) v hb
def cl_5162 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5162 v hb
def cl_5163 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5163 (by decide) v hb
def cl_5164 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5164 v hb
def cl_5165 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5165 (by decide) v hb
def cl_5166 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5166 v hb
def cl_5167 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5167 (by decide) v hb
def cl_5168 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5168 (by decide) v hb
def cl_5169 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5169 (by decide) v hb
def cl_5170 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5170 (by decide) v hb
def cl_5171 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5171 (by decide) v hb
def cl_5172 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5172 (by decide) v hb
def cl_5173 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5173 (by decide) v hb
def cl_5174 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5174 (by decide) v hb
def cl_5175 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5175 (by decide) v hb
def cl_5176 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inp_5176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5176 (by decide) v hb
def cl_5177 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5177 (by decide) v hb
def cl_5178 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5178 (by decide) v hb
def cl_5179 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5179 (by decide) v hb
def cl_5180 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5180 (by decide) v hb
def cl_5181 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5181 (by decide) v hb
def cl_5182 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5182 (by decide) v hb
def cl_5183 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5183 (by decide) v hb
def cl_5184 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inp_5184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5184 (by decide) v hb
def cl_5185 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5185 (by decide) v hb
def cl_5186 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5186 (by decide) v hb
def cl_5187 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5187 (by decide) v hb
def cl_5188 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5188 (by decide) v hb
def cl_5189 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5189 (by decide) v hb
def cl_5190 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5190 (by decide) v hb
def cl_5191 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5191 (by decide) v hb
def cl_5192 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inp_5192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5192 (by decide) v hb
def cl_5193 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5193 (by decide) v hb
def cl_5194 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5194 (by decide) v hb
def cl_5195 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5195 (by decide) v hb
def cl_5196 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inp_5196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5196 (by decide) v hb
end Percolation.NReplay
