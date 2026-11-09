import Inputs001
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_211 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,true),(25,false)]
theorem inp_211 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_211 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_211 (by decide) v h
def cl_212 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,true),(25,false)]
theorem inp_212 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_212 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_212 (by decide) v h
def cl_214 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,true),(25,false)]
theorem inp_214 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_214 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_214 (by decide) v h
def cl_215 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,true),(25,false)]
theorem inp_215 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_215 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_215 (by decide) v h
def cl_216 : CNF.NClause := [(65,true),(3,true),(8,true),(13,true),(18,false),(23,true),(25,false)]
theorem inp_216 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_216 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_216 (by decide) v h
def cl_219 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,true),(25,false)]
theorem inp_219 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_219 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_219 (by decide) v h
def cl_220 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,true),(23,true),(25,false)]
theorem inp_220 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_220 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_220 (by decide) v h
def cl_221 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,true),(25,false)]
theorem inp_221 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_221 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_221 (by decide) v h
def cl_223 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,true),(23,true),(25,false)]
theorem inp_223 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_223 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_223 (by decide) v h
def cl_227 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,false),(25,true)]
theorem inp_227 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_227 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_227 (by decide) v h
def cl_228 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,false),(25,true)]
theorem inp_228 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_228 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_228 (by decide) v h
def cl_231 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,false),(25,true)]
theorem inp_231 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_231 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_231 (by decide) v h
def cl_232 : CNF.NClause := [(65,true),(3,true),(8,true),(13,true),(18,false),(23,false),(25,true)]
theorem inp_232 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_232 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_232 (by decide) v h
def cl_234 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,true),(23,false),(25,true)]
theorem inp_234 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_234 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_234 (by decide) v h
def cl_235 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,false),(25,true)]
theorem inp_235 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_235 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_235 (by decide) v h
def cl_236 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,true),(23,false),(25,true)]
theorem inp_236 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_236 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_236 (by decide) v h
def cl_237 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,false),(25,true)]
theorem inp_237 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_237 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_237 (by decide) v h
def cl_238 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,true),(23,false),(25,true)]
theorem inp_238 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_238 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_238 (by decide) v h
def cl_239 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,true),(23,false),(25,true)]
theorem inp_239 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_239 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_239 (by decide) v h
def cl_240 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,true),(23,false),(25,true)]
theorem inp_240 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_240 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_240 (by decide) v h
def cl_243 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,true),(25,true)]
theorem inp_243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_243 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_243 (by decide) v h
def cl_244 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,true),(25,true)]
theorem inp_244 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_244 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_244 (by decide) v h
def cl_247 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,true),(25,true)]
theorem inp_247 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_247 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_247 (by decide) v h
def cl_248 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,false),(23,true),(25,true)]
theorem inp_248 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_248 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_248 (by decide) v h
def cl_251 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,true),(25,true)]
theorem inp_251 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_251 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_251 (by decide) v h
def cl_252 : CNF.NClause := [(65,false),(3,true),(8,true),(13,false),(18,true),(23,true),(25,true)]
theorem inp_252 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_252 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_252 (by decide) v h
def cl_253 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,true),(25,true)]
theorem inp_253 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_253 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_253 (by decide) v h
def cl_255 : CNF.NClause := [(65,false),(3,false),(8,true),(13,true),(18,true),(23,true),(25,true)]
theorem inp_255 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_255 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_255 (by decide) v h
def cl_256 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,true),(23,true),(25,true)]
theorem inp_256 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_256 := by
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) cl_256 (by decide) v h
def cl_257 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,false),(21,false),(25,false)]
theorem inp_257 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_257 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_257 (by decide) v h
def cl_258 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,false),(25,false)]
theorem inp_258 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_258 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_258 (by decide) v h
def cl_259 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,false),(25,false)]
theorem inp_259 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_259 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_259 (by decide) v h
def cl_260 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,false),(21,false),(25,false)]
theorem inp_260 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_260 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_260 (by decide) v h
def cl_261 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,false),(25,false)]
theorem inp_261 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_261 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_261 (by decide) v h
def cl_262 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,false),(21,false),(25,false)]
theorem inp_262 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_262 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_262 (by decide) v h
def cl_263 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,false),(21,false),(25,false)]
theorem inp_263 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_263 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_263 (by decide) v h
def cl_264 : CNF.NClause := [(66,true),(1,true),(6,true),(11,true),(16,false),(21,false),(25,false)]
theorem inp_264 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_264 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_264 (by decide) v h
def cl_267 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,false),(25,false)]
theorem inp_267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_267 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_267 (by decide) v h
def cl_268 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,true),(21,false),(25,false)]
theorem inp_268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_268 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_268 (by decide) v h
def cl_269 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,false),(25,false)]
theorem inp_269 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_269 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_269 (by decide) v h
def cl_272 : CNF.NClause := [(66,true),(1,true),(6,true),(11,true),(16,true),(21,false),(25,false)]
theorem inp_272 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_272 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_272 (by decide) v h
def cl_274 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,true),(25,false)]
theorem inp_274 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_274 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_274 (by decide) v h
def cl_275 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,true),(25,false)]
theorem inp_275 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_275 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_275 (by decide) v h
def cl_277 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,true),(25,false)]
theorem inp_277 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_277 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_277 (by decide) v h
def cl_281 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,true),(21,true),(25,false)]
theorem inp_281 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_281 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_281 (by decide) v h
def cl_282 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,true),(25,false)]
theorem inp_282 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_282 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_282 (by decide) v h
def cl_283 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,true),(25,false)]
theorem inp_283 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_283 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_283 (by decide) v h
def cl_285 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,true),(25,false)]
theorem inp_285 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_285 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_285 (by decide) v h
def cl_286 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,true),(21,true),(25,false)]
theorem inp_286 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_286 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_286 (by decide) v h
def cl_287 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,true),(21,true),(25,false)]
theorem inp_287 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_287 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_287 (by decide) v h
end Percolation.Replay
