import Inputs000
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_138 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,false),(25,false)]
theorem inp_138 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_138 (by decide) v h
def cl_139 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,false),(25,false)]
theorem inp_139 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_139 (by decide) v h
def cl_140 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,true),(22,false),(25,false)]
theorem inp_140 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_140 (by decide) v h
def cl_141 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,true),(22,false),(25,false)]
theorem inp_141 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_141 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_141 (by decide) v h
def cl_142 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,true),(22,false),(25,false)]
theorem inp_142 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_142 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_142 (by decide) v h
def cl_143 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,true),(22,false),(25,false)]
theorem inp_143 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_143 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_143 (by decide) v h
def cl_144 : CNF.NClause := [(64,true),(2,true),(7,true),(12,true),(17,true),(22,false),(25,false)]
theorem inp_144 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_144 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_144 (by decide) v h
def cl_145 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,false),(22,true),(25,false)]
theorem inp_145 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_145 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_145 (by decide) v h
def cl_146 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,true),(25,false)]
theorem inp_146 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_146 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_146 (by decide) v h
def cl_147 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,true),(25,false)]
theorem inp_147 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_147 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_147 (by decide) v h
def cl_148 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,true),(25,false)]
theorem inp_148 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_148 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_148 (by decide) v h
def cl_149 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,false),(22,true),(25,false)]
theorem inp_149 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_149 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_149 (by decide) v h
def cl_150 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,true),(25,false)]
theorem inp_150 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_150 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_150 (by decide) v h
def cl_151 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,true),(25,false)]
theorem inp_151 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_151 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_151 (by decide) v h
def cl_152 : CNF.NClause := [(64,true),(2,true),(7,true),(12,true),(17,false),(22,true),(25,false)]
theorem inp_152 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_152 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_152 (by decide) v h
def cl_153 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,true),(25,false)]
theorem inp_153 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_153 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_153 (by decide) v h
def cl_154 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,true),(25,false)]
theorem inp_154 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_154 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_154 (by decide) v h
def cl_155 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,true),(25,false)]
theorem inp_155 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_155 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_155 (by decide) v h
def cl_156 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,true),(22,true),(25,false)]
theorem inp_156 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_156 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_156 (by decide) v h
def cl_159 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,true),(22,true),(25,false)]
theorem inp_159 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_159 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_159 (by decide) v h
def cl_161 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,false),(22,false),(25,true)]
theorem inp_161 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_161 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_161 (by decide) v h
def cl_162 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,false),(25,true)]
theorem inp_162 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_162 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_162 (by decide) v h
def cl_163 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,false),(25,true)]
theorem inp_163 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_163 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_163 (by decide) v h
def cl_164 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,false),(25,true)]
theorem inp_164 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_164 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_164 (by decide) v h
def cl_165 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,false),(22,false),(25,true)]
theorem inp_165 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_165 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_165 (by decide) v h
def cl_166 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,false),(25,true)]
theorem inp_166 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_166 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_166 (by decide) v h
def cl_167 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,false),(25,true)]
theorem inp_167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_167 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_167 (by decide) v h
def cl_168 : CNF.NClause := [(64,true),(2,true),(7,true),(12,true),(17,false),(22,false),(25,true)]
theorem inp_168 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_168 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_168 (by decide) v h
def cl_169 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,false),(25,true)]
theorem inp_169 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_169 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_169 (by decide) v h
def cl_171 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,false),(25,true)]
theorem inp_171 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_171 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_171 (by decide) v h
def cl_172 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,true),(22,false),(25,true)]
theorem inp_172 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_172 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_172 (by decide) v h
def cl_175 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,true),(22,false),(25,true)]
theorem inp_175 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_175 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_175 (by decide) v h
def cl_179 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,true),(25,true)]
theorem inp_179 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_179 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_179 (by decide) v h
def cl_180 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,true),(25,true)]
theorem inp_180 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_180 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_180 (by decide) v h
def cl_183 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,true),(25,true)]
theorem inp_183 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_183 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_183 (by decide) v h
def cl_185 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,true),(25,true)]
theorem inp_185 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_185 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_185 (by decide) v h
def cl_187 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,true),(25,true)]
theorem inp_187 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_187 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_187 (by decide) v h
def cl_193 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,false),(23,false),(25,false)]
theorem inp_193 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_193 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_193 (by decide) v h
def cl_194 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,false),(25,false)]
theorem inp_194 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_194 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_194 (by decide) v h
def cl_195 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,false),(25,false)]
theorem inp_195 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_195 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_195 (by decide) v h
def cl_196 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,false),(25,false)]
theorem inp_196 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_196 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_196 (by decide) v h
def cl_198 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,false),(25,false)]
theorem inp_198 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_198 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_198 (by decide) v h
def cl_199 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,false),(25,false)]
theorem inp_199 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_199 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_199 (by decide) v h
def cl_200 : CNF.NClause := [(65,true),(3,true),(8,true),(13,true),(18,false),(23,false),(25,false)]
theorem inp_200 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_200 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_200 (by decide) v h
def cl_203 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,false),(25,false)]
theorem inp_203 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_203 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_203 (by decide) v h
def cl_204 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,true),(23,false),(25,false)]
theorem inp_204 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_204 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_204 (by decide) v h
def cl_205 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,false),(25,false)]
theorem inp_205 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_205 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_205 (by decide) v h
def cl_207 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,true),(23,false),(25,false)]
theorem inp_207 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_207 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_207 (by decide) v h
def cl_208 : CNF.NClause := [(65,true),(3,true),(8,true),(13,true),(18,true),(23,false),(25,false)]
theorem inp_208 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_208 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_208 (by decide) v h
def cl_210 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,true),(25,false)]
theorem inp_210 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_210 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_210 (by decide) v h
end Percolation.Replay
