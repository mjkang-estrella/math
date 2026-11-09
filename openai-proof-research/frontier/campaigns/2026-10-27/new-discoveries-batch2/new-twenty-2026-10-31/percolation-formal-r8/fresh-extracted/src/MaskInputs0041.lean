import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2331 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,true),(61,false)]
theorem inputList2331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2331 (by decide) v hb
mask_input "2331|2317102008282120192|316912650057115897169331617792"
def inputClause2332 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,true),(55,true),(61,false)]
theorem inputList2332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2332 (by decide) v hb
mask_input "2332|2314850208468434944|316912650057118148969145303040"
def inputClause2333 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,true),(61,false)]
theorem inputList2333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2333 (by decide) v hb
mask_input "2333|2312598408654749696|316912650057120400768958988288"
def inputClause2335 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,true),(55,true),(61,false)]
theorem inputList2335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2335 (by decide) v hb
mask_input "2335|2308094809027379200|316912650057124904368586358784"
def inputClause2337 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,false),(61,true)]
theorem inputList2337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2337 (by decide) v hb
mask_input "2337|69805794224242688|316912650059363193383389495296"
def inputClause2338 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,false),(61,true)]
theorem inputList2338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2338 (by decide) v hb
mask_input "2338|67553994410557440|316912650059365445183203180544"
def inputClause2339 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,false),(61,true)]
theorem inputList2339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2339 (by decide) v hb
mask_input "2339|65302194596872192|316912650059367696983016865792"
def inputClause2340 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,false),(61,true)]
theorem inputList2340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2340 (by decide) v hb
mask_input "2340|63050394783186944|316912650059369948782830551040"
def inputClause2341 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,false),(61,true)]
theorem inputList2341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2341 (by decide) v hb
mask_input "2341|60798594969501696|316912650059372200582644236288"
def inputClause2342 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,false),(61,true)]
theorem inputList2342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2342 (by decide) v hb
mask_input "2342|58546795155816448|316912650059374452382457921536"
def inputClause2343 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,false),(61,true)]
theorem inputList2343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2343 (by decide) v hb
mask_input "2343|56294995342131200|316912650059376704182271606784"
def inputClause2344 : CNF.NClause := [(98,true),(51,true),(52,true),(53,true),(54,false),(55,false),(61,true)]
theorem inputList2344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2344 (by decide) v hb
mask_input "2344|54043195528445952|316912650059378955982085292032"
def inputClause2345 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,false),(61,true)]
theorem inputList2345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2345 (by decide) v hb
mask_input "2345|51791395714760704|316912650059381207781898977280"
def inputClause2346 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,false),(61,true)]
theorem inputList2346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2346 (by decide) v hb
mask_input "2346|49539595901075456|316912650059383459581712662528"
def inputClause2347 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,false),(61,true)]
theorem inputList2347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2347 (by decide) v hb
mask_input "2347|47287796087390208|316912650059385711381526347776"
def inputClause2348 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,true),(55,false),(61,true)]
theorem inputList2348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2348 (by decide) v hb
mask_input "2348|45035996273704960|316912650059387963181340033024"
def inputClause2349 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,false),(61,true)]
theorem inputList2349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2349 (by decide) v hb
mask_input "2349|42784196460019712|316912650059390214981153718272"
def inputClause2350 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,true),(55,false),(61,true)]
theorem inputList2350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2350 (by decide) v hb
mask_input "2350|40532396646334464|316912650059392466780967403520"
def inputClause2351 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,true),(55,false),(61,true)]
theorem inputList2351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2351 (by decide) v hb
mask_input "2351|38280596832649216|316912650059394718580781088768"
def inputClause2353 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,true),(61,true)]
theorem inputList2353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2353 (by decide) v hb
mask_input "2353|33776997205278720|316912650059399222180408459264"
def inputClause2354 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,true),(61,true)]
theorem inputList2354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2354 (by decide) v hb
mask_input "2354|31525197391593472|316912650059401473980222144512"
def inputClause2355 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,true),(61,true)]
theorem inputList2355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2355 (by decide) v hb
mask_input "2355|29273397577908224|316912650059403725780035829760"
def inputClause2356 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,true),(61,true)]
theorem inputList2356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2356 (by decide) v hb
mask_input "2356|27021597764222976|316912650059405977579849515008"
def inputClause2357 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,true),(61,true)]
theorem inputList2357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2357 (by decide) v hb
mask_input "2357|24769797950537728|316912650059408229379663200256"
def inputClause2358 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,true),(61,true)]
theorem inputList2358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2358 (by decide) v hb
mask_input "2358|22517998136852480|316912650059410481179476885504"
def inputClause2359 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,true),(61,true)]
theorem inputList2359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2359 (by decide) v hb
mask_input "2359|20266198323167232|316912650059412732979290570752"
def inputClause2361 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,true),(61,true)]
theorem inputList2361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2361 (by decide) v hb
mask_input "2361|15762598695796736|316912650059417236578917941248"
def inputClause2362 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,true),(61,true)]
theorem inputList2362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2362 (by decide) v hb
mask_input "2362|13510798882111488|316912650059419488378731626496"
def inputClause2363 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,true),(61,true)]
theorem inputList2363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2363 (by decide) v hb
mask_input "2363|11258999068426240|316912650059421740178545311744"
def inputClause2365 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,true),(61,true)]
theorem inputList2365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2365 (by decide) v hb
mask_input "2365|6755399441055744|316912650059426243778172682240"
def inputClause2367 : CNF.NClause := [(98,false),(51,false),(52,true),(53,true),(54,true),(55,true),(61,true)]
theorem inputList2367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2367 (by decide) v hb
mask_input "2367|316912650057059602173989486592|2373397003624251392"
def inputClause2368 : CNF.NClause := [(98,false),(51,true),(52,true),(53,true),(54,true),(55,true),(61,true)]
theorem inputList2368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2368 (by decide) v hb
mask_input "2368|316912650057057350374175801344|2375648803437936640"
def inputClause2369 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,false),(60,false)]
theorem inputList2369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2369 (by decide) v hb
mask_input "2369|1155323422117462016|633825300114114700748351602688"
def inputClause2370 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,false),(60,false)]
theorem inputList2370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2370 (by decide) v hb
mask_input "2370|1155323387757723648|633825300114114700782711341056"
def inputClause2371 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,false),(60,false)]
theorem inputList2371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2371 (by decide) v hb
mask_input "2371|1155322872361648128|633825300114114701298107416576"
def inputClause2372 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,false),(60,false)]
theorem inputList2372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2372 (by decide) v hb
mask_input "2372|1155322838001909760|633825300114114701332467154944"
def inputClause2373 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,false),(60,false)]
theorem inputList2373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2373 (by decide) v hb
mask_input "2373|1155314626024439808|633825300114114709544444624896"
def inputClause2374 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,false),(60,false)]
theorem inputList2374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2374 (by decide) v hb
mask_input "2374|1155314591664701440|633825300114114709578804363264"
def inputClause2375 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,false),(60,false)]
theorem inputList2375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2375 (by decide) v hb
mask_input "2375|1155314076268625920|633825300114114710094200438784"
def inputClause2376 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,false),(51,false),(60,false)]
theorem inputList2376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2376 (by decide) v hb
mask_input "2376|1155314041908887552|633825300114114710128560177152"
end Percolation.MaskChain
