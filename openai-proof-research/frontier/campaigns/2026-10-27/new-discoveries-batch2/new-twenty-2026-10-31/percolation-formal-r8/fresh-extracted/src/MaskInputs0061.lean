import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3204 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,false),(59,false)]
theorem inputList3204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3204 (by decide) v hb
mask_input "3204|594554315650105344|5192296858534827628531600135815168"
def inputClause3205 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,false),(59,false)]
theorem inputList3205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3205 (by decide) v hb
mask_input "3205|594546623363678208|5192296858534827628539292422242304"
def inputClause3206 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,false),(59,false)]
theorem inputList3206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3206 (by decide) v hb
mask_input "3206|594546619068710912|5192296858534827628539296717209600"
def inputClause3207 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,false),(59,false)]
theorem inputList3207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3207 (by decide) v hb
mask_input "3207|594545523852050432|5192296858534827628540391933870080"
def inputClause3208 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,false),(59,false)]
theorem inputList3208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3208 (by decide) v hb
mask_input "3208|594545519557083136|5192296858534827628540396228837376"
def inputClause3209 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,false),(59,false)]
theorem inputList3209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3209 (by decide) v hb
mask_input "3209|594485050712522752|5192296858534827628600865073397760"
def inputClause3210 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,false),(59,false)]
theorem inputList3210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3210 (by decide) v hb
mask_input "3210|594485046417555456|5192296858534827628600869368365056"
def inputClause3211 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,false),(59,false)]
theorem inputList3211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3211 (by decide) v hb
mask_input "3211|594483951200894976|5192296858534827628601964585025536"
def inputClause3212 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,true),(54,false),(59,false)]
theorem inputList3212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3212 (by decide) v hb
mask_input "3212|594483946905927680|5192296858534827628601968879992832"
def inputClause3213 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,false),(59,false)]
theorem inputList3213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3213 (by decide) v hb
mask_input "3213|594476254619500544|5192296858534827628609661166419968"
def inputClause3214 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,true),(54,false),(59,false)]
theorem inputList3214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3214 (by decide) v hb
mask_input "3214|594476250324533248|5192296858534827628609665461387264"
def inputClause3215 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,false),(59,false)]
theorem inputList3215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3215 (by decide) v hb
mask_input "3215|594475155107872768|5192296858534827628610760678047744"
def inputClause3216 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,true),(54,false),(59,false)]
theorem inputList3216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3216 (by decide) v hb
mask_input "3216|594475150812905472|5192296858534827628610764973015040"
def inputClause3217 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,true),(59,false)]
theorem inputList3217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3217 (by decide) v hb
mask_input "3217|576541020947218432|5192296858534827646544894838702080"
def inputClause3218 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,true),(59,false)]
theorem inputList3218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3218 (by decide) v hb
mask_input "3218|576541016652251136|5192296858534827646544899133669376"
def inputClause3219 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,true),(59,false)]
theorem inputList3219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3219 (by decide) v hb
mask_input "3219|576539921435590656|5192296858534827646545994350329856"
def inputClause3220 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,true),(59,false)]
theorem inputList3220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3220 (by decide) v hb
mask_input "3220|576539917140623360|5192296858534827646545998645297152"
def inputClause3221 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,true),(59,false)]
theorem inputList3221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3221 (by decide) v hb
mask_input "3221|576532224854196224|5192296858534827646553690931724288"
def inputClause3222 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,true),(59,false)]
theorem inputList3222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3222 (by decide) v hb
mask_input "3222|576532220559228928|5192296858534827646553695226691584"
def inputClause3223 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,true),(59,false)]
theorem inputList3223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3223 (by decide) v hb
mask_input "3223|576531125342568448|5192296858534827646554790443352064"
def inputClause3224 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,true),(59,false)]
theorem inputList3224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3224 (by decide) v hb
mask_input "3224|576531121047601152|5192296858534827646554794738319360"
def inputClause3225 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,true),(59,false)]
theorem inputList3225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3225 (by decide) v hb
mask_input "3225|576470652203040768|5192296858534827646615263582879744"
def inputClause3226 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,true),(59,false)]
theorem inputList3226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3226 (by decide) v hb
mask_input "3226|576470647908073472|5192296858534827646615267877847040"
def inputClause3227 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,true),(59,false)]
theorem inputList3227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3227 (by decide) v hb
mask_input "3227|576469552691412992|5192296858534827646616363094507520"
def inputClause3228 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,true),(54,true),(59,false)]
theorem inputList3228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3228 (by decide) v hb
mask_input "3228|576469548396445696|5192296858534827646616367389474816"
def inputClause3229 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,true),(54,true),(59,false)]
theorem inputList3229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3229 (by decide) v hb
mask_input "3229|576461856110018560|5192296858534827646624059675901952"
def inputClause3230 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,true),(54,true),(59,false)]
theorem inputList3230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3230 (by decide) v hb
mask_input "3230|576461851815051264|5192296858534827646624063970869248"
def inputClause3231 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,true),(54,true),(59,false)]
theorem inputList3231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3231 (by decide) v hb
mask_input "3231|576460756598390784|5192296858534827646625159187529728"
def inputClause3232 : CNF.NClause := [(112,false),(32,true),(40,true),(43,true),(46,true),(54,true),(59,false)]
theorem inputList3232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3232 (by decide) v hb
mask_input "3232|5192296858534828204991248632643584|18094667153276928"
def inputClause3233 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,false),(59,true)]
theorem inputList3233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3233 (by decide) v hb
mask_input "3233|18094667153276928|5192296858534828204991248632643584"
def inputClause3234 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,false),(59,true)]
theorem inputList3234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3234 (by decide) v hb
mask_input "3234|18094662858309632|5192296858534828204991252927610880"
def inputClause3235 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,false),(59,true)]
theorem inputList3235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3235 (by decide) v hb
mask_input "3235|18093567641649152|5192296858534828204992348144271360"
def inputClause3236 : CNF.NClause := [(112,true),(32,true),(40,true),(43,false),(46,false),(54,false),(59,true)]
theorem inputList3236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3236 (by decide) v hb
mask_input "3236|18093563346681856|5192296858534828204992352439238656"
def inputClause3237 : CNF.NClause := [(112,true),(32,false),(40,false),(43,true),(46,false),(54,false),(59,true)]
theorem inputList3237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3237 (by decide) v hb
mask_input "3237|18085871060254720|5192296858534828205000044725665792"
def inputClause3238 : CNF.NClause := [(112,true),(32,true),(40,false),(43,true),(46,false),(54,false),(59,true)]
theorem inputList3238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3238 (by decide) v hb
mask_input "3238|18085866765287424|5192296858534828205000049020633088"
def inputClause3239 : CNF.NClause := [(112,true),(32,false),(40,true),(43,true),(46,false),(54,false),(59,true)]
theorem inputList3239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3239 (by decide) v hb
mask_input "3239|18084771548626944|5192296858534828205001144237293568"
def inputClause3240 : CNF.NClause := [(112,true),(32,true),(40,true),(43,true),(46,false),(54,false),(59,true)]
theorem inputList3240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3240 (by decide) v hb
mask_input "3240|18084767253659648|5192296858534828205001148532260864"
def inputClause3241 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,true),(54,false),(59,true)]
theorem inputList3241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3241 (by decide) v hb
mask_input "3241|18024298409099264|5192296858534828205061617376821248"
def inputClause3242 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,true),(54,false),(59,true)]
theorem inputList3242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3242 (by decide) v hb
mask_input "3242|18024294114131968|5192296858534828205061621671788544"
def inputClause3243 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,false),(59,true)]
theorem inputList3243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3243 (by decide) v hb
mask_input "3243|18023198897471488|5192296858534828205062716888449024"
end Percolation.MaskChain
