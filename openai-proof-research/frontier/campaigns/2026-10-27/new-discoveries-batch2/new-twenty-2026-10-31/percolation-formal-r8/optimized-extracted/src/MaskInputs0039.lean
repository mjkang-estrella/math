import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2235 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,true),(56,true)]
theorem inputList2235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2235 (by decide) v hb
mask_input "2235|17609365913600|79228162514354973085800595456"
def inputClause2237 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,true),(56,true)]
theorem inputList2237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2237 (by decide) v hb
mask_input "2237|566935683072|79228162514354990128230825984"
def inputClause2239 : CNF.NClause := [(96,false),(34,false),(39,true),(44,true),(49,true),(54,true),(56,true)]
theorem inputList2239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2239 (by decide) v hb
mask_input "2239|79228162514264337610723819520|90653084442689536"
def inputClause2240 : CNF.NClause := [(96,false),(34,true),(39,true),(44,true),(49,true),(54,true),(56,true)]
theorem inputList2240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2240 (by decide) v hb
mask_input "2240|79228162514264337593543950336|90653101622558720"
def inputClause2241 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,false),(56,false)]
theorem inputList2241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2241 (by decide) v hb
mask_input "2241|76706470934085632|158456325028528675187087900672"
def inputClause2242 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,false),(56,false)]
theorem inputList2242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2242 (by decide) v hb
mask_input "2242|76706466639118336|158456325028528675191382867968"
def inputClause2243 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,false),(56,false)]
theorem inputList2243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2243 (by decide) v hb
mask_input "2243|76706333495132160|158456325028528675324526854144"
def inputClause2244 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,false),(52,false),(56,false)]
theorem inputList2244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2244 (by decide) v hb
mask_input "2244|76706329200164864|158456325028528675328821821440"
def inputClause2245 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,false),(56,false)]
theorem inputList2245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2245 (by decide) v hb
mask_input "2245|76702072887574528|158456325028528679585134411776"
def inputClause2246 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,false),(56,false)]
theorem inputList2246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2246 (by decide) v hb
mask_input "2246|76702068592607232|158456325028528679589429379072"
def inputClause2247 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,false),(56,false)]
theorem inputList2247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2247 (by decide) v hb
mask_input "2247|76701935448621056|158456325028528679722573365248"
def inputClause2248 : CNF.NClause := [(97,true),(32,true),(37,true),(42,true),(47,false),(52,false),(56,false)]
theorem inputList2248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2248 (by decide) v hb
mask_input "2248|76701931153653760|158456325028528679726868332544"
def inputClause2249 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,true),(52,false),(56,false)]
theorem inputList2249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2249 (by decide) v hb
mask_input "2249|76565733445730304|158456325028528815924576256000"
def inputClause2250 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,false),(56,false)]
theorem inputList2250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2250 (by decide) v hb
mask_input "2250|76565729150763008|158456325028528815928871223296"
def inputClause2251 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,false),(56,false)]
theorem inputList2251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2251 (by decide) v hb
mask_input "2251|76565596006776832|158456325028528816062015209472"
def inputClause2252 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,true),(52,false),(56,false)]
theorem inputList2252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2252 (by decide) v hb
mask_input "2252|76565591711809536|158456325028528816066310176768"
def inputClause2253 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,true),(52,false),(56,false)]
theorem inputList2253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2253 (by decide) v hb
mask_input "2253|76561335399219200|158456325028528820322622767104"
def inputClause2254 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,true),(52,false),(56,false)]
theorem inputList2254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2254 (by decide) v hb
mask_input "2254|76561331104251904|158456325028528820326917734400"
def inputClause2255 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,true),(52,false),(56,false)]
theorem inputList2255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2255 (by decide) v hb
mask_input "2255|76561197960265728|158456325028528820460061720576"
def inputClause2257 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,true),(56,false)]
theorem inputList2257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2257 (by decide) v hb
mask_input "2257|72202871306715136|158456325028533178786715271168"
def inputClause2258 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,true),(56,false)]
theorem inputList2258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2258 (by decide) v hb
mask_input "2258|72202867011747840|158456325028533178791010238464"
def inputClause2259 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,true),(56,false)]
theorem inputList2259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2259 (by decide) v hb
mask_input "2259|72202733867761664|158456325028533178924154224640"
def inputClause2261 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,true),(56,false)]
theorem inputList2261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2261 (by decide) v hb
mask_input "2261|72198473260204032|158456325028533183184761782272"
def inputClause2262 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,true),(56,false)]
theorem inputList2262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2262 (by decide) v hb
mask_input "2262|72198468965236736|158456325028533183189056749568"
def inputClause2263 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,true),(56,false)]
theorem inputList2263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2263 (by decide) v hb
mask_input "2263|72198335821250560|158456325028533183322200735744"
def inputClause2266 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,true),(56,false)]
theorem inputList2266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2266 (by decide) v hb
mask_input "2266|72062129523392512|158456325028533319528498593792"
def inputClause2267 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,true),(56,false)]
theorem inputList2267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2267 (by decide) v hb
mask_input "2267|72061996379406336|158456325028533319661642579968"
def inputClause2272 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,true),(52,true),(56,false)]
theorem inputList2272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2272 (by decide) v hb
mask_input "2272|158456325028600732781125828608|4648876896157696"
def inputClause2273 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,false),(56,true)]
theorem inputList2273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2273 (by decide) v hb
mask_input "2273|4648876896157696|158456325028600732781125828608"
def inputClause2274 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,false),(56,true)]
theorem inputList2274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2274 (by decide) v hb
mask_input "2274|4648872601190400|158456325028600732785420795904"
def inputClause2275 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,false),(56,true)]
theorem inputList2275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2275 (by decide) v hb
mask_input "2275|4648739457204224|158456325028600732918564782080"
def inputClause2276 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,false),(52,false),(56,true)]
theorem inputList2276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2276 (by decide) v hb
mask_input "2276|4648735162236928|158456325028600732922859749376"
def inputClause2277 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,false),(56,true)]
theorem inputList2277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2277 (by decide) v hb
mask_input "2277|4644478849646592|158456325028600737179172339712"
def inputClause2278 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,false),(56,true)]
theorem inputList2278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2278 (by decide) v hb
mask_input "2278|4644474554679296|158456325028600737183467307008"
def inputClause2279 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,false),(56,true)]
theorem inputList2279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2279 (by decide) v hb
mask_input "2279|4644341410693120|158456325028600737316611293184"
def inputClause2280 : CNF.NClause := [(97,true),(32,true),(37,true),(42,true),(47,false),(52,false),(56,true)]
theorem inputList2280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2280 (by decide) v hb
mask_input "2280|4644337115725824|158456325028600737320906260480"
def inputClause2281 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,true),(52,false),(56,true)]
theorem inputList2281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2281 (by decide) v hb
mask_input "2281|4508139407802368|158456325028600873518614183936"
def inputClause2282 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,false),(56,true)]
theorem inputList2282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2282 (by decide) v hb
mask_input "2282|4508135112835072|158456325028600873522909151232"
def inputClause2283 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,false),(56,true)]
theorem inputList2283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2283 (by decide) v hb
mask_input "2283|4508001968848896|158456325028600873656053137408"
def inputClause2284 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,true),(52,false),(56,true)]
theorem inputList2284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2284 (by decide) v hb
mask_input "2284|4507997673881600|158456325028600873660348104704"
end Percolation.MaskChain
