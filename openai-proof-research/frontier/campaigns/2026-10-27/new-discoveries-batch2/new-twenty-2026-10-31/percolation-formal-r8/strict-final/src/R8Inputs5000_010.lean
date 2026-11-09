import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4320 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,false),(87,true)]
theorem inputList4320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4320 (by decide) v hb
mask_input "4320|19342813113834075385233408|155366466028965759945801732"
def inputClause4321 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4321 (by decide) v hb
mask_input "4321|623961118293234173345796|174085318024506601157689344"
def inputClause4322 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4322 (by decide) v hb
mask_input "4322|623961118293234173345792|174085318024506601157689348"
def inputClause4323 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4323 (by decide) v hb
mask_input "4323|623942671549160463794180|174085336471250674867240960"
def inputClause4324 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4324 (by decide) v hb
mask_input "4324|623942671549160463794176|174085336471250674867240964"
def inputClause4325 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4325 (by decide) v hb
mask_input "4325|623370822482875467694084|174085908320316959863341056"
def inputClause4326 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4326 (by decide) v hb
mask_input "4326|623370822482875467694080|174085908320316959863341060"
def inputClause4327 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4327 (by decide) v hb
mask_input "4327|623352375738801758142468|174085926767061033572892672"
def inputClause4328 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,true),(87,true)]
theorem inputList4328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4328 (by decide) v hb
mask_input "4328|623352375738801758142464|174085926767061033572892676"
def inputClause4329 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4329 (by decide) v hb
mask_input "4329|605071652361755592491012|174104207490438079738544128"
def inputClause4330 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4330 (by decide) v hb
mask_input "4330|605071652361755592491008|174104207490438079738544132"
def inputClause4331 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4331 (by decide) v hb
mask_input "4331|605053205617681882939396|174104225937182153448095744"
def inputClause4332 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4332 (by decide) v hb
mask_input "4332|605053205617681882939392|174104225937182153448095748"
def inputClause4333 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4333 (by decide) v hb
mask_input "4333|604481356551396886839300|174104797786248438444195840"
def inputClause4334 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4334 (by decide) v hb
mask_input "4334|604481356551396886839296|174104797786248438444195844"
def inputClause4335 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4335 (by decide) v hb
mask_input "4335|604462909807323177287684|174104816232992512153747456"
def inputClause4336 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,true),(87,true)]
theorem inputList4336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4336 (by decide) v hb
mask_input "4336|604462909807323177287680|174104816232992512153747460"
def inputClause4337 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4337 (by decide) v hb
mask_input "4337|19498208485919585992708|174689780934313915745042432"
def inputClause4338 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4338 (by decide) v hb
mask_input "4338|19498208485919585992704|174689780934313915745042436"
def inputClause4339 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4339 (by decide) v hb
mask_input "4339|19479761741845876441092|174689799381057989454594048"
def inputClause4340 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4340 (by decide) v hb
mask_input "4340|19479761741845876441088|174689799381057989454594052"
def inputClause4341 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4341 (by decide) v hb
mask_input "4341|18907912675560880340996|174690371230124274450694144"
def inputClause4342 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4342 (by decide) v hb
mask_input "4342|18907912675560880340992|174690371230124274450694148"
def inputClause4343 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4343 (by decide) v hb
mask_input "4343|18889465931487170789380|174690389676868348160245760"
def inputClause4344 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,true),(87,true)]
theorem inputList4344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4344 (by decide) v hb
mask_input "4344|18889465931487170789376|174690389676868348160245764"
def inputClause4346 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,true),(87,true)]
theorem inputList4346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4346 (by decide) v hb
mask_input "4346|608742554441005137920|174708670400245394325897220"
def inputClause4348 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,true),(87,true)]
theorem inputList4348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4348 (by decide) v hb
mask_input "4348|590295810367295586304|174708688846989468035448836"
def inputClause4350 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,true),(87,true)]
theorem inputList4350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4350 (by decide) v hb
mask_input "4350|18446744082299486208|174709260696055753031548932"
def inputClause4351 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,true),(84,true),(87,true)]
theorem inputList4351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4351 (by decide) v hb
mask_input "4351|8589934596|174709279142799826741100544"
def inputClause4352 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,true),(87,true)]
theorem inputList4352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4352 (by decide) v hb
mask_input "4352|8589934592|174709279142799826741100548"
def inputClause4353 : CNF.NClause := [(34,true),(3,false),(65,false),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4353 (by decide) v hb
mask_input "4353|194676053374927119119810568|17179869184"
def inputClause4354 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4354 (by decide) v hb
mask_input "4354|194676053374927136299679744|8"
def inputClause4355 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4355 (by decide) v hb
mask_input "4355|194676016481438988880576520|36893488147419103232"
def inputClause4356 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4356 (by decide) v hb
mask_input "4356|194676016481438988880576512|36893488147419103240"
def inputClause4357 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4357 (by decide) v hb
mask_input "4357|194674872783306418888376328|1180591620717411303424"
def inputClause4358 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4358 (by decide) v hb
mask_input "4358|194674872783306418888376320|1180591620717411303432"
def inputClause4359 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4359 (by decide) v hb
mask_input "4359|194674835889818271469273096|1217485108864830406656"
def inputClause4360 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,false),(87,false)]
theorem inputList4360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4360 (by decide) v hb
mask_input "4360|194674835889818271469273088|1217485108864830406664"
def inputClause4361 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4361 (by decide) v hb
mask_input "4361|194638274443064179137970184|37778931862957161709568"
def inputClause4362 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4362 (by decide) v hb
mask_input "4362|194638274443064179137970176|37778931862957161709576"
end Percolation.MaskChain
