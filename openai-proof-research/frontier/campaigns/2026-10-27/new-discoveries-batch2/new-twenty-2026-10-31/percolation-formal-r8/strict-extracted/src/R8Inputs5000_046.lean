import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6378 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6378 (by decide) v hb
mask_input "6378|151742917313284725014528|2553260775759062556270133248"
def inputClause6379 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6379 (by decide) v hb
mask_input "6379|151706023825137306173440|2553260812652550703688974336"
def inputClause6380 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6380 (by decide) v hb
mask_input "6380|151706023825137305911296|2553260812652550703689236480"
def inputClause6381 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6381 (by decide) v hb
mask_input "6381|151152621502926019624960|2553261366054872914975522816"
def inputClause6382 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6382 (by decide) v hb
mask_input "6382|151152621502926019362816|2553261366054872914975784960"
def inputClause6383 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6383 (by decide) v hb
mask_input "6383|151115728014778600521728|2553261402948361062394626048"
def inputClause6384 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6384 (by decide) v hb
mask_input "6384|151115728014778600259584|2553261402948361062394888192"
def inputClause6385 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6385 (by decide) v hb
mask_input "6385|10071922827195368865792|2553402446753548645626281984"
def inputClause6386 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6386 (by decide) v hb
mask_input "6386|10071922827195368603648|2553402446753548645626544128"
def inputClause6387 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6387 (by decide) v hb
mask_input "6387|10035029339047949762560|2553402483647036793045385216"
def inputClause6388 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6388 (by decide) v hb
mask_input "6388|10035029339047949500416|2553402483647036793045647360"
def inputClause6389 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6389 (by decide) v hb
mask_input "6389|9481627016836663214080|2553403037049359004331933696"
def inputClause6390 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6390 (by decide) v hb
mask_input "6390|9481627016836662951936|2553403037049359004332195840"
def inputClause6391 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6391 (by decide) v hb
mask_input "6391|9444733528689244110848|2553403073942847151751036928"
def inputClause6392 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inputList6392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6392 (by decide) v hb
mask_input "6392|9444733528689243848704|2553403073942847151751299072"
def inputClause6394 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,true),(91,true)]
theorem inputList6394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6394 (by decide) v hb
mask_input "6394|627189861456078176256|2553411891486514384916971520"
def inputClause6396 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,true),(91,true)]
theorem inputList6396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6396 (by decide) v hb
mask_input "6396|590296373308659073024|2553411928380002532336074752"
def inputClause6397 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inputList6397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6397 (by decide) v hb
mask_input "6397|36894051097372786688|2553412481782324743622361088"
def inputClause6398 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inputList6398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6398 (by decide) v hb
mask_input "6398|36894051097372524544|2553412481782324743622623232"
def inputClause6399 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inputList6399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6399 (by decide) v hb
mask_input "6399|562949953683456|2553412518675812891041464320"
def inputClause6400 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inputList6400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6400 (by decide) v hb
mask_input "6400|562949953421312|2553412518675812891041726464"
def inputClause6401 : CNF.NClause := [(50,true),(19,false),(63,false),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6401 (by decide) v hb
mask_input "6401|1276798041113045187395321856|1125899906842624"
def inputClause6403 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6403 (by decide) v hb
mask_input "6403|1276798031890799050447388672|9223372036854775808"
def inputClause6404 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6404 (by decide) v hb
mask_input "6404|1276798031890799050446864384|9223372036855300096"
def inputClause6405 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6405 (by decide) v hb
mask_input "6405|1276795679930929652479557632|2361183241434822606848"
def inputClause6406 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6406 (by decide) v hb
mask_input "6406|1276795679930929652479033344|2361183241434823131136"
def inputClause6407 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6407 (by decide) v hb
mask_input "6407|1276795670707557615624781824|2370406613471677382656"
def inputClause6408 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6408 (by decide) v hb
mask_input "6408|1276795670707557615624257536|2370406613471677906944"
def inputClause6409 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6409 (by decide) v hb
mask_input "6409|1276779151648239608721309696|18889465931478580854784"
def inputClause6411 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6411 (by decide) v hb
mask_input "6411|1276779142424867571866533888|18898689303515435630592"
def inputClause6412 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6412 (by decide) v hb
mask_input "6412|1276779142424867571866009600|18898689303515436154880"
def inputClause6413 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6413 (by decide) v hb
mask_input "6413|1276776790464998173898702848|21250649172913403461632"
def inputClause6414 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6414 (by decide) v hb
mask_input "6414|1276776790464998173898178560|21250649172913403985920"
def inputClause6415 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6415 (by decide) v hb
mask_input "6415|1276776781241626137043927040|21259872544950258237440"
def inputClause6416 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6416 (by decide) v hb
mask_input "6416|1276776781241626137043402752|21259872544950258761728"
def inputClause6419 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6419 (by decide) v hb
mask_input "6419|1276646916163347221800550400|151124950823865501614080"
def inputClause6420 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6420 (by decide) v hb
mask_input "6420|1276646916163347221800026112|151124950823865502138368"
def inputClause6421 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6421 (by decide) v hb
mask_input "6421|1276644564203477823832719360|153476910693263469445120"
def inputClause6422 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6422 (by decide) v hb
mask_input "6422|1276644564203477823832195072|153476910693263469969408"
def inputClause6423 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6423 (by decide) v hb
mask_input "6423|1276644554980105786977943552|153486134065300324220928"
end Percolation.MaskChain
