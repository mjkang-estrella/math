import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4276 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4276 (by decide) v hb
mask_input "4276|154761984672414380238831616|19947294470385455092203524"
def inputClause4277 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4277 (by decide) v hb
mask_input "4277|154761412823348095242731524|19947866319451740088303616"
def inputClause4278 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4278 (by decide) v hb
mask_input "4278|154761412823348095242731520|19947866319451740088303620"
def inputClause4279 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4279 (by decide) v hb
mask_input "4279|154761394376604021533179908|19947884766195813797855232"
def inputClause4280 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4280 (by decide) v hb
mask_input "4280|154761394376604021533179904|19947884766195813797855236"
def inputClause4281 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4281 (by decide) v hb
mask_input "4281|154743113653226975367528452|19966165489572859963506688"
def inputClause4282 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4282 (by decide) v hb
mask_input "4282|154743113653226975367528448|19966165489572859963506692"
def inputClause4283 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4283 (by decide) v hb
mask_input "4283|154743095206482901657976836|19966183936316933673058304"
def inputClause4284 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4284 (by decide) v hb
mask_input "4284|154743095206482901657976832|19966183936316933673058308"
def inputClause4285 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4285 (by decide) v hb
mask_input "4285|154742523357416616661876740|19966755785383218669158400"
def inputClause4286 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4286 (by decide) v hb
mask_input "4286|154742523357416616661876736|19966755785383218669158404"
def inputClause4287 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4287 (by decide) v hb
mask_input "4287|154742504910672542952325124|19966774232127292378710016"
def inputClause4288 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,true),(87,false)]
theorem inputList4288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4288 (by decide) v hb
mask_input "4288|154742504910672542952325120|19966774232127292378710020"
def inputClause4289 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4289 (by decide) v hb
mask_input "4289|19966774232127300968644612|154742504910672534362390528"
def inputClause4290 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4290 (by decide) v hb
mask_input "4290|19966774232127300968644608|154742504910672534362390532"
def inputClause4291 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4291 (by decide) v hb
mask_input "4291|19966755785383227259092996|154742523357416608071942144"
def inputClause4293 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4293 (by decide) v hb
mask_input "4293|19966183936316942262992900|154743095206482893068042240"
def inputClause4294 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4294 (by decide) v hb
mask_input "4294|19966183936316942262992896|154743095206482893068042244"
def inputClause4295 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4295 (by decide) v hb
mask_input "4295|19966165489572868553441284|154743113653226966777593856"
def inputClause4296 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4296 (by decide) v hb
mask_input "4296|19966165489572868553441280|154743113653226966777593860"
def inputClause4297 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inputList4297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4297 (by decide) v hb
mask_input "4297|19947884766195822387789828|154761394376604012943245312"
def inputClause4298 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inputList4298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4298 (by decide) v hb
mask_input "4298|19947884766195822387789824|154761394376604012943245316"
def inputClause4299 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inputList4299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4299 (by decide) v hb
mask_input "4299|19947866319451748678238212|154761412823348086652796928"
def inputClause4300 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,false),(87,true)]
theorem inputList4300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4300 (by decide) v hb
mask_input "4300|19947866319451748678238208|154761412823348086652796932"
def inputClause4301 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,false),(87,true)]
theorem inputList4301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4301 (by decide) v hb
mask_input "4301|19947294470385463682138116|154761984672414371648897024"
def inputClause4302 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,false),(87,true)]
theorem inputList4302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4302 (by decide) v hb
mask_input "4302|19947294470385463682138112|154761984672414371648897028"
def inputClause4304 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,false),(87,true)]
theorem inputList4304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4304 (by decide) v hb
mask_input "4304|19947276023641389972586496|154762003119158445358448644"
def inputClause4305 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4305 (by decide) v hb
mask_input "4305|19362311322319986381291524|155346967820479848949743616"
def inputClause4306 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4306 (by decide) v hb
mask_input "4306|19362311322319986381291520|155346967820479848949743620"
def inputClause4307 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4307 (by decide) v hb
mask_input "4307|19362292875575912671739908|155346986267223922659295232"
def inputClause4308 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4308 (by decide) v hb
mask_input "4308|19362292875575912671739904|155346986267223922659295236"
def inputClause4309 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4309 (by decide) v hb
mask_input "4309|19361721026509627675639812|155347558116290207655395328"
def inputClause4310 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4310 (by decide) v hb
mask_input "4310|19361721026509627675639808|155347558116290207655395332"
def inputClause4311 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4311 (by decide) v hb
mask_input "4311|19361702579765553966088196|155347576563034281364946944"
def inputClause4312 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,false),(87,true)]
theorem inputList4312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4312 (by decide) v hb
mask_input "4312|19361702579765553966088192|155347576563034281364946948"
def inputClause4313 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inputList4313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4313 (by decide) v hb
mask_input "4313|19343421856388507800436740|155365857286411327530598400"
def inputClause4314 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inputList4314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4314 (by decide) v hb
mask_input "4314|19343421856388507800436736|155365857286411327530598404"
def inputClause4315 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inputList4315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4315 (by decide) v hb
mask_input "4315|19343403409644434090885124|155365875733155401240150016"
def inputClause4316 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,false),(87,true)]
theorem inputList4316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4316 (by decide) v hb
mask_input "4316|19343403409644434090885120|155365875733155401240150020"
def inputClause4318 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,false),(87,true)]
theorem inputList4318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4318 (by decide) v hb
mask_input "4318|19342831560578149094785024|155366447582221686236250116"
end Percolation.MaskChain
