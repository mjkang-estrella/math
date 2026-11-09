import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2285 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,true),(52,false),(56,true)]
theorem inputList2285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2285 (by decide) v hb
mask_input "2285|4503741361291264|158456325028600877916660695040"
def inputClause2286 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,true),(52,false),(56,true)]
theorem inputList2286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2286 (by decide) v hb
mask_input "2286|4503737066323968|158456325028600877920955662336"
def inputClause2287 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,true),(52,false),(56,true)]
theorem inputList2287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2287 (by decide) v hb
mask_input "2287|4503603922337792|158456325028600878054099648512"
def inputClause2289 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,false),(52,true),(56,true)]
theorem inputList2289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2289 (by decide) v hb
mask_input "2289|145277268787200|158456325028605236380753199104"
def inputClause2290 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,false),(52,true),(56,true)]
theorem inputList2290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2290 (by decide) v hb
mask_input "2290|145272973819904|158456325028605236385048166400"
def inputClause2291 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,false),(52,true),(56,true)]
theorem inputList2291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2291 (by decide) v hb
mask_input "2291|145139829833728|158456325028605236518192152576"
def inputClause2292 : CNF.NClause := [(97,true),(32,true),(37,true),(42,false),(47,false),(52,true),(56,true)]
theorem inputList2292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2292 (by decide) v hb
mask_input "2292|145135534866432|158456325028605236522487119872"
def inputClause2293 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,true),(56,true)]
theorem inputList2293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2293 (by decide) v hb
mask_input "2293|140879222276096|158456325028605240778799710208"
def inputClause2294 : CNF.NClause := [(97,true),(32,true),(37,false),(42,true),(47,false),(52,true),(56,true)]
theorem inputList2294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2294 (by decide) v hb
mask_input "2294|140874927308800|158456325028605240783094677504"
def inputClause2295 : CNF.NClause := [(97,true),(32,false),(37,true),(42,true),(47,false),(52,true),(56,true)]
theorem inputList2295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2295 (by decide) v hb
mask_input "2295|140741783322624|158456325028605240916238663680"
def inputClause2297 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(47,true),(52,true),(56,true)]
theorem inputList2297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2297 (by decide) v hb
mask_input "2297|4539780431872|158456325028605377118241554432"
def inputClause2298 : CNF.NClause := [(97,true),(32,true),(37,false),(42,false),(47,true),(52,true),(56,true)]
theorem inputList2298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2298 (by decide) v hb
mask_input "2298|4535485464576|158456325028605377122536521728"
def inputClause2299 : CNF.NClause := [(97,true),(32,false),(37,true),(42,false),(47,true),(52,true),(56,true)]
theorem inputList2299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2299 (by decide) v hb
mask_input "2299|4402341478400|158456325028605377255680507904"
def inputClause2301 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,true),(52,true),(56,true)]
theorem inputList2301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2301 (by decide) v hb
mask_input "2301|141733920768|158456325028605381516288065536"
def inputClause2304 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,true),(52,true),(56,true)]
theorem inputList2304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2304 (by decide) v hb
mask_input "2304|158456325028528675187087900672|76706470934085632"
def inputClause2305 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,false),(61,false)]
theorem inputList2305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2305 (by decide) v hb
mask_input "2305|2375648803437936640|316912650057057350374175801344"
def inputClause2306 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,false),(61,false)]
theorem inputList2306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2306 (by decide) v hb
mask_input "2306|2373397003624251392|316912650057059602173989486592"
def inputClause2307 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,false),(61,false)]
theorem inputList2307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2307 (by decide) v hb
mask_input "2307|2371145203810566144|316912650057061853973803171840"
def inputClause2308 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,false),(61,false)]
theorem inputList2308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2308 (by decide) v hb
mask_input "2308|2368893403996880896|316912650057064105773616857088"
def inputClause2309 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,false),(61,false)]
theorem inputList2309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2309 (by decide) v hb
mask_input "2309|2366641604183195648|316912650057066357573430542336"
def inputClause2310 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,false),(61,false)]
theorem inputList2310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2310 (by decide) v hb
mask_input "2310|2364389804369510400|316912650057068609373244227584"
def inputClause2311 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,false),(61,false)]
theorem inputList2311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2311 (by decide) v hb
mask_input "2311|2362138004555825152|316912650057070861173057912832"
def inputClause2312 : CNF.NClause := [(98,true),(51,true),(52,true),(53,true),(54,false),(55,false),(61,false)]
theorem inputList2312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2312 (by decide) v hb
mask_input "2312|2359886204742139904|316912650057073112972871598080"
def inputClause2313 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,false),(61,false)]
theorem inputList2313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2313 (by decide) v hb
mask_input "2313|2357634404928454656|316912650057075364772685283328"
def inputClause2314 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,false),(61,false)]
theorem inputList2314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2314 (by decide) v hb
mask_input "2314|2355382605114769408|316912650057077616572498968576"
def inputClause2315 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,true),(55,false),(61,false)]
theorem inputList2315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2315 (by decide) v hb
mask_input "2315|2353130805301084160|316912650057079868372312653824"
def inputClause2316 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,true),(55,false),(61,false)]
theorem inputList2316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2316 (by decide) v hb
mask_input "2316|2350879005487398912|316912650057082120172126339072"
def inputClause2317 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,true),(55,false),(61,false)]
theorem inputList2317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2317 (by decide) v hb
mask_input "2317|2348627205673713664|316912650057084371971940024320"
def inputClause2318 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,true),(55,false),(61,false)]
theorem inputList2318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2318 (by decide) v hb
mask_input "2318|2346375405860028416|316912650057086623771753709568"
def inputClause2319 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,true),(55,false),(61,false)]
theorem inputList2319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2319 (by decide) v hb
mask_input "2319|2344123606046343168|316912650057088875571567394816"
def inputClause2321 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,false),(55,true),(61,false)]
theorem inputList2321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2321 (by decide) v hb
mask_input "2321|2339620006418972672|316912650057093379171194765312"
def inputClause2322 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,false),(55,true),(61,false)]
theorem inputList2322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2322 (by decide) v hb
mask_input "2322|2337368206605287424|316912650057095630971008450560"
def inputClause2323 : CNF.NClause := [(98,true),(51,false),(52,true),(53,false),(54,false),(55,true),(61,false)]
theorem inputList2323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2323 (by decide) v hb
mask_input "2323|2335116406791602176|316912650057097882770822135808"
def inputClause2324 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(55,true),(61,false)]
theorem inputList2324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2324 (by decide) v hb
mask_input "2324|2332864606977916928|316912650057100134570635821056"
def inputClause2325 : CNF.NClause := [(98,true),(51,false),(52,false),(53,true),(54,false),(55,true),(61,false)]
theorem inputList2325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2325 (by decide) v hb
mask_input "2325|2330612807164231680|316912650057102386370449506304"
def inputClause2326 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(55,true),(61,false)]
theorem inputList2326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2326 (by decide) v hb
mask_input "2326|2328361007350546432|316912650057104638170263191552"
def inputClause2327 : CNF.NClause := [(98,true),(51,false),(52,true),(53,true),(54,false),(55,true),(61,false)]
theorem inputList2327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2327 (by decide) v hb
mask_input "2327|2326109207536861184|316912650057106889970076876800"
def inputClause2328 : CNF.NClause := [(98,true),(51,true),(52,true),(53,true),(54,false),(55,true),(61,false)]
theorem inputList2328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2328 (by decide) v hb
mask_input "2328|2323857407723175936|316912650057109141769890562048"
def inputClause2329 : CNF.NClause := [(98,true),(51,false),(52,false),(53,false),(54,true),(55,true),(61,false)]
theorem inputList2329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2329 (by decide) v hb
mask_input "2329|2321605607909490688|316912650057111393569704247296"
def inputClause2330 : CNF.NClause := [(98,true),(51,true),(52,false),(53,false),(54,true),(55,true),(61,false)]
theorem inputList2330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2330 (by decide) v hb
mask_input "2330|2319353808095805440|316912650057113645369517932544"
end Percolation.MaskChain
