import NInputs000
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_164 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,false),(25,true)]
theorem inp_164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_164 v hb
def cl_165 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,false),(22,false),(25,true)]
theorem inp_165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_165 v hb
def cl_166 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,false),(25,true)]
theorem inp_166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_166 v hb
def cl_167 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,false),(25,true)]
theorem inp_167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_167 v hb
def cl_168 : CNF.NClause := [(64,true),(2,true),(7,true),(12,true),(17,false),(22,false),(25,true)]
theorem inp_168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_168 v hb
def cl_169 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,false),(25,true)]
theorem inp_169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_169 v hb
def cl_170 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,false),(25,true)]
theorem inp_170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_170 (by decide) v hb
def cl_171 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,false),(25,true)]
theorem inp_171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_171 v hb
def cl_172 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,true),(22,false),(25,true)]
theorem inp_172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_172 v hb
def cl_173 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,true),(22,false),(25,true)]
theorem inp_173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_173 (by decide) v hb
def cl_174 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,true),(22,false),(25,true)]
theorem inp_174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_174 (by decide) v hb
def cl_175 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,true),(22,false),(25,true)]
theorem inp_175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_175 v hb
def cl_176 : CNF.NClause := [(64,false),(2,true),(7,true),(12,true),(17,true),(22,false),(25,true)]
theorem inp_176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_176 (by decide) v hb
def cl_177 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,false),(22,true),(25,true)]
theorem inp_177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_177 (by decide) v hb
def cl_178 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,true),(25,true)]
theorem inp_178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_178 (by decide) v hb
def cl_179 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,true),(25,true)]
theorem inp_179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_179 v hb
def cl_180 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,true),(25,true)]
theorem inp_180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_180 v hb
def cl_181 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,false),(22,true),(25,true)]
theorem inp_181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_181 (by decide) v hb
def cl_182 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,true),(25,true)]
theorem inp_182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_182 (by decide) v hb
def cl_183 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,true),(25,true)]
theorem inp_183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_183 v hb
def cl_184 : CNF.NClause := [(64,false),(2,true),(7,true),(12,true),(17,false),(22,true),(25,true)]
theorem inp_184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_184 (by decide) v hb
def cl_185 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,true),(25,true)]
theorem inp_185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_185 v hb
def cl_186 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,true),(25,true)]
theorem inp_186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_186 (by decide) v hb
def cl_187 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,true),(25,true)]
theorem inp_187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_187 v hb
def cl_188 : CNF.NClause := [(64,false),(2,true),(7,true),(12,false),(17,true),(22,true),(25,true)]
theorem inp_188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_188 (by decide) v hb
def cl_189 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,true),(22,true),(25,true)]
theorem inp_189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_189 (by decide) v hb
def cl_190 : CNF.NClause := [(64,false),(2,true),(7,false),(12,true),(17,true),(22,true),(25,true)]
theorem inp_190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_190 (by decide) v hb
def cl_191 : CNF.NClause := [(64,false),(2,false),(7,true),(12,true),(17,true),(22,true),(25,true)]
theorem inp_191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_191 (by decide) v hb
def cl_192 : CNF.NClause := [(64,false),(2,true),(7,true),(12,true),(17,true),(22,true),(25,true)]
theorem inp_192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_192 (by decide) v hb
def cl_225 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,false),(23,false),(25,true)]
theorem inp_225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_225 (by decide) v hb
def cl_226 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,false),(25,true)]
theorem inp_226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_226 (by decide) v hb
def cl_227 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,false),(25,true)]
theorem inp_227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_227 v hb
def cl_228 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,false),(25,true)]
theorem inp_228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_228 v hb
def cl_229 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,false),(23,false),(25,true)]
theorem inp_229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_229 (by decide) v hb
def cl_230 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,false),(25,true)]
theorem inp_230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_230 (by decide) v hb
def cl_231 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,false),(25,true)]
theorem inp_231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_231 v hb
def cl_232 : CNF.NClause := [(65,true),(3,true),(8,true),(13,true),(18,false),(23,false),(25,true)]
theorem inp_232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_232 v hb
def cl_233 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,true),(23,false),(25,true)]
theorem inp_233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_233 (by decide) v hb
def cl_234 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,true),(23,false),(25,true)]
theorem inp_234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_234 v hb
def cl_235 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,false),(25,true)]
theorem inp_235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_235 v hb
def cl_236 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,true),(23,false),(25,true)]
theorem inp_236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_236 v hb
def cl_237 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,false),(25,true)]
theorem inp_237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_237 v hb
def cl_238 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,true),(23,false),(25,true)]
theorem inp_238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_238 v hb
def cl_239 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,true),(23,false),(25,true)]
theorem inp_239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_239 v hb
def cl_240 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,true),(23,false),(25,true)]
theorem inp_240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_240 v hb
def cl_241 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,false),(23,true),(25,true)]
theorem inp_241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_241 (by decide) v hb
def cl_242 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,true),(25,true)]
theorem inp_242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_242 (by decide) v hb
def cl_243 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,true),(25,true)]
theorem inp_243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_243 v hb
def cl_244 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,true),(25,true)]
theorem inp_244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_244 v hb
def cl_245 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,false),(23,true),(25,true)]
theorem inp_245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_245 (by decide) v hb
end Percolation.NReplay
