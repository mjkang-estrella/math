import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3244 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,true),(54,false),(59,true)]
theorem inputList3244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3244 (by decide) v hb
mask_input "3244|18023194602504192|5192296858534828205062721183416320"
def inputClause3245 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,false),(59,true)]
theorem inputList3245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3245 (by decide) v hb
mask_input "3245|18015502316077056|5192296858534828205070413469843456"
def inputClause3246 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,true),(54,false),(59,true)]
theorem inputList3246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3246 (by decide) v hb
mask_input "3246|18015498021109760|5192296858534828205070417764810752"
def inputClause3247 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,false),(59,true)]
theorem inputList3247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3247 (by decide) v hb
mask_input "3247|18014402804449280|5192296858534828205071512981471232"
def inputClause3249 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,true),(59,true)]
theorem inputList3249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3249 (by decide) v hb
mask_input "3249|80268643794944|5192296858534828223005647142125568"
def inputClause3250 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,true),(59,true)]
theorem inputList3250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3250 (by decide) v hb
mask_input "3250|80264348827648|5192296858534828223005651437092864"
def inputClause3251 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,true),(59,true)]
theorem inputList3251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3251 (by decide) v hb
mask_input "3251|79169132167168|5192296858534828223006746653753344"
def inputClause3252 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,true),(59,true)]
theorem inputList3252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3252 (by decide) v hb
mask_input "3252|79164837199872|5192296858534828223006750948720640"
def inputClause3253 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,true),(59,true)]
theorem inputList3253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3253 (by decide) v hb
mask_input "3253|71472550772736|5192296858534828223014443235147776"
def inputClause3254 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,true),(59,true)]
theorem inputList3254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3254 (by decide) v hb
mask_input "3254|71468255805440|5192296858534828223014447530115072"
def inputClause3255 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,true),(59,true)]
theorem inputList3255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3255 (by decide) v hb
mask_input "3255|70373039144960|5192296858534828223015542746775552"
def inputClause3257 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,true),(59,true)]
theorem inputList3257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3257 (by decide) v hb
mask_input "3257|9899899617280|5192296858534828223076015886303232"
def inputClause3258 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,true),(59,true)]
theorem inputList3258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3258 (by decide) v hb
mask_input "3258|9895604649984|5192296858534828223076020181270528"
def inputClause3259 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,true),(59,true)]
theorem inputList3259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3259 (by decide) v hb
mask_input "3259|8800387989504|5192296858534828223077115397931008"
def inputClause3261 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,true),(59,true)]
theorem inputList3261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3261 (by decide) v hb
mask_input "3261|1103806595072|5192296858534828223084811979325440"
def inputClause3264 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,true),(54,true),(59,true)]
theorem inputList3264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3264 (by decide) v hb
mask_input "3264|5192296858534827628530496329220096|594555419456700416"
def inputClause3265 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,false),(61,false)]
theorem inputList3265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3265 (by decide) v hb
mask_input "3265|2305845139517472768|10384593717069655257060992658440192"
def inputClause3266 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,false),(61,false)]
theorem inputList3266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3266 (by decide) v hb
mask_input "3266|2305845070797996032|10384593717069655257061061377916928"
def inputClause3267 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,false),(61,false)]
theorem inputList3267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3267 (by decide) v hb
mask_input "3267|2305845002078519296|10384593717069655257061130097393664"
def inputClause3268 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,false),(61,false)]
theorem inputList3268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3268 (by decide) v hb
mask_input "3268|2305844933359042560|10384593717069655257061198816870400"
def inputClause3269 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,false),(61,false)]
theorem inputList3269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3269 (by decide) v hb
mask_input "3269|2305844864639565824|10384593717069655257061267536347136"
def inputClause3270 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,false),(61,false)]
theorem inputList3270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3270 (by decide) v hb
mask_input "3270|2305844795920089088|10384593717069655257061336255823872"
def inputClause3271 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,false),(61,false)]
theorem inputList3271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3271 (by decide) v hb
mask_input "3271|2305844727200612352|10384593717069655257061404975300608"
def inputClause3272 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,false),(61,false)]
theorem inputList3272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3272 (by decide) v hb
mask_input "3272|2305844658481135616|10384593717069655257061473694777344"
def inputClause3273 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,false),(61,false)]
theorem inputList3273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3273 (by decide) v hb
mask_input "3273|2305844589761658880|10384593717069655257061542414254080"
def inputClause3274 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,false),(61,false)]
theorem inputList3274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3274 (by decide) v hb
mask_input "3274|2305844521042182144|10384593717069655257061611133730816"
def inputClause3275 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,false),(61,false)]
theorem inputList3275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3275 (by decide) v hb
mask_input "3275|2305844452322705408|10384593717069655257061679853207552"
def inputClause3276 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,true),(40,false),(61,false)]
theorem inputList3276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3276 (by decide) v hb
mask_input "3276|2305844383603228672|10384593717069655257061748572684288"
def inputClause3277 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,false),(61,false)]
theorem inputList3277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3277 (by decide) v hb
mask_input "3277|2305844314883751936|10384593717069655257061817292161024"
def inputClause3278 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,true),(40,false),(61,false)]
theorem inputList3278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3278 (by decide) v hb
mask_input "3278|2305844246164275200|10384593717069655257061886011637760"
def inputClause3279 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,true),(40,false),(61,false)]
theorem inputList3279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3279 (by decide) v hb
mask_input "3279|2305844177444798464|10384593717069655257061954731114496"
def inputClause3281 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,true),(61,false)]
theorem inputList3281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3281 (by decide) v hb
mask_input "3281|2305844040005844992|10384593717069655257062092170067968"
def inputClause3282 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,true),(61,false)]
theorem inputList3282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3282 (by decide) v hb
mask_input "3282|2305843971286368256|10384593717069655257062160889544704"
def inputClause3283 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,true),(61,false)]
theorem inputList3283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3283 (by decide) v hb
mask_input "3283|2305843902566891520|10384593717069655257062229609021440"
def inputClause3284 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,true),(61,false)]
theorem inputList3284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3284 (by decide) v hb
mask_input "3284|2305843833847414784|10384593717069655257062298328498176"
def inputClause3285 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,true),(61,false)]
theorem inputList3285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3285 (by decide) v hb
mask_input "3285|2305843765127938048|10384593717069655257062367047974912"
def inputClause3286 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,true),(61,false)]
theorem inputList3286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3286 (by decide) v hb
mask_input "3286|2305843696408461312|10384593717069655257062435767451648"
def inputClause3287 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,true),(61,false)]
theorem inputList3287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3287 (by decide) v hb
mask_input "3287|2305843627688984576|10384593717069655257062504486928384"
def inputClause3288 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,true),(61,false)]
theorem inputList3288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3288 (by decide) v hb
mask_input "3288|2305843558969507840|10384593717069655257062573206405120"
def inputClause3289 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,true),(61,false)]
theorem inputList3289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3289 (by decide) v hb
mask_input "3289|2305843490250031104|10384593717069655257062641925881856"
end Percolation.MaskChain
