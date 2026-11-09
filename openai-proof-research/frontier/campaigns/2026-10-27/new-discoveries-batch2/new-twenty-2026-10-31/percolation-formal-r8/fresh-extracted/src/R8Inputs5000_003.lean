import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2800 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,true),(54,false),(60,true)]
theorem inputList2800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2800 (by decide) v hb
mask_input "2800|40564819207303358862293012054016|1154049749565833216"
def inputClause2808 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,false),(54,true),(60,true)]
theorem inputList2808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2808 (by decide) v hb
mask_input "2808|40564819207303341973794409414656|1170938248168472576"
def inputClause2812 : CNF.NClause := [(105,false),(33,true),(37,true),(41,false),(50,true),(54,true),(60,true)]
theorem inputList2812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2812 (by decide) v hb
mask_input "2812|40564819207303340850093525827584|1172061949052059648"
def inputClause2814 : CNF.NClause := [(105,false),(33,true),(37,false),(41,true),(50,true),(54,true),(60,true)]
theorem inputList2814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2814 (by decide) v hb
mask_input "2814|40564819207303340848031941525504|1172064010636361728"
def inputClause2815 : CNF.NClause := [(105,false),(33,false),(37,true),(41,true),(50,true),(54,true),(60,true)]
theorem inputList2815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2815 (by decide) v hb
mask_input "2815|40564819207303340847903092506624|1172064139485380608"
def inputClause2864 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,true),(53,false),(57,true)]
theorem inputList2864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2864 (by decide) v hb
mask_input "2864|81129638414606690702988259885056|144259241278963712"
def inputClause2872 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,false),(53,true),(57,true)]
theorem inputList2872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2872 (by decide) v hb
mask_input "2872|81129638414606681836526493499392|153125703045349376"
def inputClause2876 : CNF.NClause := [(106,false),(34,true),(40,true),(41,false),(47,true),(53,true),(57,true)]
theorem inputList2876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2876 (by decide) v hb
mask_input "2876|81129638414606681697988028399616|153264241510449152"
def inputClause2878 : CNF.NClause := [(106,false),(34,true),(40,false),(41,true),(47,true),(53,true),(57,true)]
theorem inputList2878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2878 (by decide) v hb
mask_input "2878|81129638414606681696888516771840|153265341022076928"
def inputClause2879 : CNF.NClause := [(106,false),(34,false),(40,true),(41,true),(47,true),(53,true),(57,true)]
theorem inputList2879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2879 (by decide) v hb
mask_input "2879|81129638414606681695806185013248|153266423353835520"
def inputClause2936 : CNF.NClause := [(107,false),(32,true),(39,true),(41,true),(48,false),(55,true),(58,true)]
theorem inputList2936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2936 (by decide) v hb
mask_input "2936|162259276829213363673052986998784|324261926244712448"
def inputClause2942 : CNF.NClause := [(107,false),(32,true),(39,false),(41,true),(48,true),(55,true),(58,true)]
theorem inputList2942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2942 (by decide) v hb
mask_input "2942|162259276829213363392127766102016|324542851465609216"
def inputClause2943 : CNF.NClause := [(107,false),(32,false),(39,true),(41,true),(48,true),(55,true),(58,true)]
theorem inputList2943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2943 (by decide) v hb
mask_input "2943|162259276829213363391582305255424|324543396926455808"
def inputClause3056 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,true),(53,false),(58,true)]
theorem inputList3056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3056 (by decide) v hb
mask_input "3056|649037107316853462573511295893504|288318508880625664"
def inputClause3064 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,false),(53,true),(58,true)]
theorem inputList3064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3064 (by decide) v hb
mask_input "3064|649037107316853453636680785330176|297255339391188992"
def inputClause3068 : CNF.NClause := [(109,false),(35,true),(37,true),(44,false),(46,true),(53,true),(58,true)]
theorem inputList3068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3068 (by decide) v hb
mask_input "3068|649037107316853453583904227196928|297308115949322240"
def inputClause3070 : CNF.NClause := [(109,false),(35,true),(37,false),(44,true),(46,true),(53,true),(58,true)]
theorem inputList3070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3070 (by decide) v hb
mask_input "3070|649037107316853453566449480105984|297325570696413184"
def inputClause3071 : CNF.NClause := [(109,false),(35,false),(37,true),(44,true),(46,true),(53,true),(58,true)]
theorem inputList3071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3071 (by decide) v hb
mask_input "3071|649037107316853453566346400890880|297325673775628288"
def inputClause3104 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,true),(52,true),(57,false)]
theorem inputList3104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3104 (by decide) v hb
mask_input "3104|1298074214633707051247812158160896|4609711089385472"
def inputClause3120 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,true),(52,false),(57,true)]
theorem inputList3120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3120 (by decide) v hb
mask_input "3120|1298074214633706911636223709675520|144221299537870848"
def inputClause3168 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,true),(55,true),(60,false)]
theorem inputList3168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3168 (by decide) v hb
mask_input "3168|2596148429267414967186752771457024|36103855867428864"
def inputClause3184 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,true),(55,false),(60,true)]
theorem inputList3184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3184 (by decide) v hb
mask_input "3184|2596148429267413850294045183574016|1152996563455311872"
def inputClause3192 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,false),(55,true),(60,true)]
theorem inputList3192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3192 (by decide) v hb
mask_input "3192|2596148429267413814335616908787712|1188954991730098176"
def inputClause3196 : CNF.NClause := [(111,false),(34,true),(38,true),(42,false),(46,true),(55,true),(60,true)]
theorem inputList3196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3196 (by decide) v hb
mask_input "3196|2596148429267413814269646211121152|1189020962427764736"
def inputClause3198 : CNF.NClause := [(111,false),(34,true),(38,false),(42,true),(46,true),(55,true),(60,true)]
theorem inputList3198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3198 (by decide) v hb
mask_input "3198|2596148429267413814265523042516992|1189025085596368896"
def inputClause3248 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,true),(54,false),(59,true)]
theorem inputList3248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3248 (by decide) v hb
mask_input "3248|5192296858534827646544894838702080|576541020947218432"
def inputClause3256 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,false),(54,true),(59,true)]
theorem inputList3256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3256 (by decide) v hb
mask_input "3256|5192296858534827628600865073397760|594485050712522752"
def inputClause3260 : CNF.NClause := [(112,false),(32,true),(40,true),(43,false),(46,true),(54,true),(59,true)]
theorem inputList3260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3260 (by decide) v hb
mask_input "3260|5192296858534827628539292422242304|594546623363678208"
def inputClause3262 : CNF.NClause := [(112,false),(32,true),(40,false),(43,true),(46,true),(54,true),(59,true)]
theorem inputList3262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3262 (by decide) v hb
mask_input "3262|5192296858534827628531595840847872|594554319945072640"
def inputClause3263 : CNF.NClause := [(112,false),(32,false),(40,true),(43,true),(46,true),(54,true),(59,true)]
theorem inputList3263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3263 (by decide) v hb
mask_input "3263|5192296858534827628530500624187392|594555415161733120"
def inputClause3312 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,true),(40,false),(61,true)]
theorem inputList3312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3312 (by decide) v hb
mask_input "3312|10384593717069655257062092170067968|2305844040005844992"
def inputClause3320 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,false),(40,true),(61,true)]
theorem inputList3320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3320 (by decide) v hb
mask_input "3320|10384593717069655257061542414254080|2305844589761658880"
def inputClause3324 : CNF.NClause := [(113,false),(36,true),(37,true),(38,false),(39,true),(40,true),(61,true)]
theorem inputList3324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3324 (by decide) v hb
mask_input "3324|10384593717069655257061267536347136|2305844864639565824"
def inputClause3326 : CNF.NClause := [(113,false),(36,true),(37,false),(38,true),(39,true),(40,true),(61,true)]
theorem inputList3326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3326 (by decide) v hb
mask_input "3326|10384593717069655257061130097393664|2305845002078519296"
def inputClause3327 : CNF.NClause := [(113,false),(36,false),(37,true),(38,true),(39,true),(40,true),(61,true)]
theorem inputList3327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3327 (by decide) v hb
mask_input "3327|10384593717069655257061061377916928|2305845070797996032"
def inputClause3376 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,false),(57,true)]
theorem inputList3376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3376 (by decide) v hb
mask_input "3376|20769187434139310532136383826362368|144401164178292736"
def inputClause3384 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,false),(54,true),(57,true)]
theorem inputList3384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3384 (by decide) v hb
mask_input "3384|20769187434139310514403460293591040|162134087711064064"
def inputClause3388 : CNF.NClause := [(114,false),(35,true),(36,true),(42,false),(48,true),(54,true),(57,true)]
theorem inputList3388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3388 (by decide) v hb
mask_input "3388|20769187434139310514126383363391488|162411164641263616"
def inputClause3390 : CNF.NClause := [(114,false),(35,true),(36,false),(42,true),(48,true),(54,true),(57,true)]
theorem inputList3390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3390 (by decide) v hb
mask_input "3390|20769187434139310514122054036357120|162415493968297984"
def inputClause3391 : CNF.NClause := [(114,false),(35,false),(36,true),(42,true),(48,true),(54,true),(57,true)]
theorem inputList3391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3391 (by decide) v hb
mask_input "3391|20769187434139310514122019676618752|162415528328036352"
end Percolation.MaskChain
