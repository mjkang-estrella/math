import Inputs028
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3171 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,false),(60,true)]
theorem inp_3171 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3171 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3171 (by decide) v h
def cl_3172 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,false),(60,true)]
theorem inp_3172 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3172 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3172 (by decide) v h
def cl_3175 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,false),(60,true)]
theorem inp_3175 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3175 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3175 (by decide) v h
def cl_3176 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,false),(60,true)]
theorem inp_3176 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3176 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3176 (by decide) v h
def cl_3179 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,false),(60,true)]
theorem inp_3179 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3179 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3179 (by decide) v h
def cl_3180 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,false),(60,true)]
theorem inp_3180 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3180 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3180 (by decide) v h
def cl_3183 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,false),(60,true)]
theorem inp_3183 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3183 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3183 (by decide) v h
def cl_3188 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,true),(60,true)]
theorem inp_3188 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3188 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3188 (by decide) v h
def cl_3191 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,true),(60,true)]
theorem inp_3191 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3191 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3191 (by decide) v h
def cl_3201 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3201 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3201 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3201 (by decide) v h
def cl_3202 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3202 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3202 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3202 (by decide) v h
def cl_3203 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3203 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3203 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3203 (by decide) v h
def cl_3204 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,false),(59,false)]
theorem inp_3204 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3204 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3204 (by decide) v h
def cl_3205 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3205 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3205 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3205 (by decide) v h
def cl_3206 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3206 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3206 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3206 (by decide) v h
def cl_3207 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3207 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3207 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3207 (by decide) v h
def cl_3208 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,false),(59,false)]
theorem inp_3208 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3208 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3208 (by decide) v h
def cl_3209 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,false),(59,false)]
theorem inp_3209 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3209 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3209 (by decide) v h
def cl_3211 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,false),(59,false)]
theorem inp_3211 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3211 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3211 (by decide) v h
def cl_3213 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,false),(59,false)]
theorem inp_3213 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3213 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3213 (by decide) v h
def cl_3215 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,false),(59,false)]
theorem inp_3215 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3215 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3215 (by decide) v h
def cl_3217 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,true),(59,false)]
theorem inp_3217 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3217 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3217 (by decide) v h
def cl_3218 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,true),(59,false)]
theorem inp_3218 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3218 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3218 (by decide) v h
def cl_3220 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,true),(59,false)]
theorem inp_3220 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3220 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3220 (by decide) v h
def cl_3221 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3221 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3221 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3221 (by decide) v h
def cl_3222 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3222 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3222 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3222 (by decide) v h
def cl_3223 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3223 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3223 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3223 (by decide) v h
def cl_3224 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,true),(59,false)]
theorem inp_3224 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3224 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3224 (by decide) v h
def cl_3225 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,true),(59,false)]
theorem inp_3225 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3225 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3225 (by decide) v h
def cl_3227 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,true),(59,false)]
theorem inp_3227 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3227 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3227 (by decide) v h
def cl_3231 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,true),(59,false)]
theorem inp_3231 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3231 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3231 (by decide) v h
def cl_3233 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3233 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3233 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3233 (by decide) v h
def cl_3234 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3234 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3234 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3234 (by decide) v h
def cl_3235 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3235 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3235 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3235 (by decide) v h
def cl_3236 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,false),(59,true)]
theorem inp_3236 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3236 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3236 (by decide) v h
def cl_3239 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,false),(59,true)]
theorem inp_3239 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3239 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3239 (by decide) v h
def cl_3241 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,false),(59,true)]
theorem inp_3241 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3241 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3241 (by decide) v h
def cl_3243 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,false),(59,true)]
theorem inp_3243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3243 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3243 (by decide) v h
def cl_3247 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,false),(59,true)]
theorem inp_3247 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3247 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3247 (by decide) v h
def cl_3252 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,true),(59,true)]
theorem inp_3252 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3252 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3252 (by decide) v h
def cl_3253 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,true),(59,true)]
theorem inp_3253 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3253 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3253 (by decide) v h
def cl_3255 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,true),(59,true)]
theorem inp_3255 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3255 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3255 (by decide) v h
def cl_3257 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,true),(59,true)]
theorem inp_3257 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3257 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3257 (by decide) v h
def cl_3259 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,true),(59,true)]
theorem inp_3259 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3259 := by
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) cl_3259 (by decide) v h
def cl_3265 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3265 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3265 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3265 (by decide) v h
def cl_3266 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3266 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3266 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3266 (by decide) v h
def cl_3267 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3267 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3267 (by decide) v h
def cl_3268 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,false),(61,false)]
theorem inp_3268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3268 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3268 (by decide) v h
def cl_3269 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,false),(61,false)]
theorem inp_3269 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3269 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3269 (by decide) v h
def cl_3270 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,false),(61,false)]
theorem inp_3270 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3270 := by
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) cl_3270 (by decide) v h
end Percolation.Replay
