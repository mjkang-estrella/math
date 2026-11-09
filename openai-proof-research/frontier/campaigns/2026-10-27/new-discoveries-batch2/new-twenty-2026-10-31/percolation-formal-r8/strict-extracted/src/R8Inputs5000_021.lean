import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5274 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5274 (by decide) v hb
mask_input "5274|4951849882104697821878812672|56668397794435742565376"
def inputClause5275 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5275 (by decide) v hb
mask_input "5275|4951845159738214952233600000|61390764277305387778048"
def inputClause5276 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5276 (by decide) v hb
mask_input "5276|4951845159738214952233598976|61390764277305387779072"
def inputClause5277 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5277 (by decide) v hb
mask_input "5277|4951840437371732082588386304|66113130760175032991744"
def inputClause5278 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5278 (by decide) v hb
mask_input "5278|4951840437371732082588385280|66113130760175032992768"
def inputClause5279 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5279 (by decide) v hb
mask_input "5279|4951835715005249212943172608|70835497243044678205440"
def inputClause5280 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5280 (by decide) v hb
mask_input "5280|4951835715005249212943171584|70835497243044678206464"
def inputClause5281 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5281 (by decide) v hb
mask_input "5281|4951830992638766343297958912|75557863725914323419136"
def inputClause5282 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5282 (by decide) v hb
mask_input "5282|4951830992638766343297957888|75557863725914323420160"
def inputClause5283 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5283 (by decide) v hb
mask_input "5283|4951826270272283473652745216|80280230208783968632832"
def inputClause5284 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5284 (by decide) v hb
mask_input "5284|4951826270272283473652744192|80280230208783968633856"
def inputClause5285 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5285 (by decide) v hb
mask_input "5285|4951821547905800604007531520|85002596691653613846528"
def inputClause5286 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5286 (by decide) v hb
mask_input "5286|4951821547905800604007530496|85002596691653613847552"
def inputClause5287 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5287 (by decide) v hb
mask_input "5287|4951816825539317734362317824|89724963174523259060224"
def inputClause5288 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem inputList5288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5288 (by decide) v hb
mask_input "5288|4951816825539317734362316800|89724963174523259061248"
def inputClause5289 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5289 (by decide) v hb
mask_input "5289|4951812103172834864717104128|94447329657392904273920"
def inputClause5290 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5290 (by decide) v hb
mask_input "5290|4951812103172834864717103104|94447329657392904274944"
def inputClause5291 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5291 (by decide) v hb
mask_input "5291|4951807380806351995071890432|99169696140262549487616"
def inputClause5292 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5292 (by decide) v hb
mask_input "5292|4951807380806351995071889408|99169696140262549488640"
def inputClause5293 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5293 (by decide) v hb
mask_input "5293|4951802658439869125426676736|103892062623132194701312"
def inputClause5294 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5294 (by decide) v hb
mask_input "5294|4951802658439869125426675712|103892062623132194702336"
def inputClause5295 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5295 (by decide) v hb
mask_input "5295|4951797936073386255781463040|108614429106001839915008"
def inputClause5296 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,true),(92,false)]
theorem inputList5296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5296 (by decide) v hb
mask_input "5296|4951797936073386255781462016|108614429106001839916032"
def inputClause5297 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5297 (by decide) v hb
mask_input "5297|4951793213706903386136249344|113336795588871485128704"
def inputClause5298 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5298 (by decide) v hb
mask_input "5298|4951793213706903386136248320|113336795588871485129728"
def inputClause5299 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5299 (by decide) v hb
mask_input "5299|4951788491340420516491035648|118059162071741130342400"
def inputClause5300 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5300 (by decide) v hb
mask_input "5300|4951788491340420516491034624|118059162071741130343424"
def inputClause5301 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5301 (by decide) v hb
mask_input "5301|4951783768973937646845821952|122781528554610775556096"
def inputClause5302 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5302 (by decide) v hb
mask_input "5302|4951783768973937646845820928|122781528554610775557120"
def inputClause5303 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5303 (by decide) v hb
mask_input "5303|4951779046607454777200608256|127503895037480420769792"
def inputClause5304 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inputList5304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5304 (by decide) v hb
mask_input "5304|4951779046607454777200607232|127503895037480420770816"
def inputClause5305 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inputList5305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5305 (by decide) v hb
mask_input "5305|4951774324240971907555394560|132226261520350065983488"
def inputClause5306 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inputList5306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5306 (by decide) v hb
mask_input "5306|4951774324240971907555393536|132226261520350065984512"
def inputClause5307 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inputList5307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5307 (by decide) v hb
mask_input "5307|4951769601874489037910180864|136948628003219711197184"
def inputClause5308 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,true),(92,false)]
theorem inputList5308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5308 (by decide) v hb
mask_input "5308|4951769601874489037910179840|136948628003219711198208"
def inputClause5309 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,true),(92,false)]
theorem inputList5309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5309 (by decide) v hb
mask_input "5309|4951764879508006168264967168|141670994486089356410880"
def inputClause5310 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,true),(92,false)]
theorem inputList5310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5310 (by decide) v hb
mask_input "5310|4951764879508006168264966144|141670994486089356411904"
def inputClause5312 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,true),(92,false)]
theorem inputList5312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5312 (by decide) v hb
mask_input "5312|4951760157141523298619752448|146393360968959001625600"
def inputClause5313 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5313 (by decide) v hb
mask_input "5313|146393360971158024881152|4951760157141521099596496896"
def inputClause5314 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5314 (by decide) v hb
mask_input "5314|146393360971158024880128|4951760157141521099596497920"
end Percolation.MaskChain
