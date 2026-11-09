import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4235 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4235 (by decide) v hb
mask_input "4235|174690371230124283040628740|18907912675552290406400"
def inputClause4236 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4236 (by decide) v hb
mask_input "4236|174690371230124283040628736|18907912675552290406404"
def inputClause4237 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4237 (by decide) v hb
mask_input "4237|174689799381057998044528644|19479761741837286506496"
def inputClause4238 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4238 (by decide) v hb
mask_input "4238|174689799381057998044528640|19479761741837286506500"
def inputClause4239 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4239 (by decide) v hb
mask_input "4239|174689780934313924334977028|19498208485910996058112"
def inputClause4240 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4240 (by decide) v hb
mask_input "4240|174689780934313924334977024|19498208485910996058116"
def inputClause4241 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4241 (by decide) v hb
mask_input "4241|174104816232992520743682052|604462909807314587353088"
def inputClause4242 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4242 (by decide) v hb
mask_input "4242|174104816232992520743682048|604462909807314587353092"
def inputClause4243 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4243 (by decide) v hb
mask_input "4243|174104797786248447034130436|604481356551388296904704"
def inputClause4244 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4244 (by decide) v hb
mask_input "4244|174104797786248447034130432|604481356551388296904708"
def inputClause4245 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4245 (by decide) v hb
mask_input "4245|174104225937182162038030340|605053205617673293004800"
def inputClause4246 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4246 (by decide) v hb
mask_input "4246|174104225937182162038030336|605053205617673293004804"
def inputClause4247 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4247 (by decide) v hb
mask_input "4247|174104207490438088328478724|605071652361747002556416"
def inputClause4248 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inputList4248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4248 (by decide) v hb
mask_input "4248|174104207490438088328478720|605071652361747002556420"
def inputClause4249 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inputList4249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4249 (by decide) v hb
mask_input "4249|174085926767061042162827268|623352375738793168207872"
def inputClause4250 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inputList4250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4250 (by decide) v hb
mask_input "4250|174085926767061042162827264|623352375738793168207876"
def inputClause4251 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inputList4251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4251 (by decide) v hb
mask_input "4251|174085908320316968453275652|623370822482866877759488"
def inputClause4252 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inputList4252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4252 (by decide) v hb
mask_input "4252|174085908320316968453275648|623370822482866877759492"
def inputClause4253 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,true),(84,false),(87,false)]
theorem inputList4253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4253 (by decide) v hb
mask_input "4253|174085336471250683457175556|623942671549151873859584"
def inputClause4254 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,false),(87,false)]
theorem inputList4254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4254 (by decide) v hb
mask_input "4254|174085336471250683457175552|623942671549151873859588"
def inputClause4256 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,false),(87,false)]
theorem inputList4256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4256 (by decide) v hb
mask_input "4256|174085318024506609747623936|623961118293225583411204"
def inputClause4257 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4257 (by decide) v hb
mask_input "4257|155366466028965768535736324|19342813113834066795298816"
def inputClause4258 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4258 (by decide) v hb
mask_input "4258|155366466028965768535736320|19342813113834066795298820"
def inputClause4259 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4259 (by decide) v hb
mask_input "4259|155366447582221694826184708|19342831560578140504850432"
def inputClause4260 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4260 (by decide) v hb
mask_input "4260|155366447582221694826184704|19342831560578140504850436"
def inputClause4261 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4261 (by decide) v hb
mask_input "4261|155365875733155409830084612|19343403409644425500950528"
def inputClause4262 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4262 (by decide) v hb
mask_input "4262|155365875733155409830084608|19343403409644425500950532"
def inputClause4263 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4263 (by decide) v hb
mask_input "4263|155365857286411336120532996|19343421856388499210502144"
def inputClause4264 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inputList4264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4264 (by decide) v hb
mask_input "4264|155365857286411336120532992|19343421856388499210502148"
def inputClause4265 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4265 (by decide) v hb
mask_input "4265|155347576563034289954881540|19361702579765545376153600"
def inputClause4266 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4266 (by decide) v hb
mask_input "4266|155347576563034289954881536|19361702579765545376153604"
def inputClause4267 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4267 (by decide) v hb
mask_input "4267|155347558116290216245329924|19361721026509619085705216"
def inputClause4268 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4268 (by decide) v hb
mask_input "4268|155347558116290216245329920|19361721026509619085705220"
def inputClause4269 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4269 (by decide) v hb
mask_input "4269|155346986267223931249229828|19362292875575904081805312"
def inputClause4270 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4270 (by decide) v hb
mask_input "4270|155346986267223931249229824|19362292875575904081805316"
def inputClause4271 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4271 (by decide) v hb
mask_input "4271|155346967820479857539678212|19362311322319977791356928"
def inputClause4272 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inputList4272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4272 (by decide) v hb
mask_input "4272|155346967820479857539678208|19362311322319977791356932"
def inputClause4273 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4273 (by decide) v hb
mask_input "4273|154762003119158453948383236|19947276023641381382651904"
def inputClause4274 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4274 (by decide) v hb
mask_input "4274|154762003119158453948383232|19947276023641381382651908"
def inputClause4275 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inputList4275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4275 (by decide) v hb
mask_input "4275|154761984672414380238831620|19947294470385455092203520"
end Percolation.MaskChain
