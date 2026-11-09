import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4444 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4444 (by decide) v hb
mask_input "4444|38686806819288868181770240|155989246555638268117909512"
def inputClause4445 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4445 (by decide) v hb
mask_input "4445|38685663121156298189570056|155990390253770838110109696"
def inputClause4446 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4446 (by decide) v hb
mask_input "4446|38685663121156298189570048|155990390253770838110109704"
def inputClause4447 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4447 (by decide) v hb
mask_input "4447|38685626227668150770466824|155990427147258985529212928"
def inputClause4448 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4448 (by decide) v hb
mask_input "4448|38685626227668150770466816|155990427147258985529212936"
def inputClause4449 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4449 (by decide) v hb
mask_input "4449|1247922236586468346691592|193428131138340667952988160"
def inputClause4450 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4450 (by decide) v hb
mask_input "4450|1247922236586468346691584|193428131138340667952988168"
def inputClause4451 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4451 (by decide) v hb
mask_input "4451|1247885343098320927588360|193428168031828815372091392"
def inputClause4452 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4452 (by decide) v hb
mask_input "4452|1247885343098320927588352|193428168031828815372091400"
def inputClause4453 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4453 (by decide) v hb
mask_input "4453|1246741644965750935388168|193429311729961385364291584"
def inputClause4454 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4454 (by decide) v hb
mask_input "4454|1246741644965750935388160|193429311729961385364291592"
def inputClause4455 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4455 (by decide) v hb
mask_input "4455|1246704751477603516284936|193429348623449532783394816"
def inputClause4456 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem inputList4456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4456 (by decide) v hb
mask_input "4456|1246704751477603516284928|193429348623449532783394824"
def inputClause4457 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4457 (by decide) v hb
mask_input "4457|1210143304723511184982024|193465910070203625114697728"
def inputClause4458 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4458 (by decide) v hb
mask_input "4458|1210143304723511184982016|193465910070203625114697736"
def inputClause4459 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4459 (by decide) v hb
mask_input "4459|1210106411235363765878792|193465946963691772533800960"
def inputClause4460 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4460 (by decide) v hb
mask_input "4460|1210106411235363765878784|193465946963691772533800968"
def inputClause4461 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4461 (by decide) v hb
mask_input "4461|1208962713102793773678600|193467090661824342526001152"
def inputClause4462 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4462 (by decide) v hb
mask_input "4462|1208962713102793773678592|193467090661824342526001160"
def inputClause4463 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4463 (by decide) v hb
mask_input "4463|1208925819614646354575368|193467127555312489945104384"
def inputClause4464 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,true),(87,true)]
theorem inputList4464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4464 (by decide) v hb
mask_input "4464|1208925819614646354575360|193467127555312489945104392"
def inputClause4465 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4465 (by decide) v hb
mask_input "4465|38996416971839171985416|194637056957955297127694336"
def inputClause4466 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4466 (by decide) v hb
mask_input "4466|38996416971839171985408|194637056957955297127694344"
def inputClause4467 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4467 (by decide) v hb
mask_input "4467|38959523483691752882184|194637093851443444546797568"
def inputClause4468 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4468 (by decide) v hb
mask_input "4468|38959523483691752882176|194637093851443444546797576"
def inputClause4469 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4469 (by decide) v hb
mask_input "4469|37815825351121760681992|194638237549576014538997760"
def inputClause4470 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4470 (by decide) v hb
mask_input "4470|37815825351121760681984|194638237549576014538997768"
def inputClause4471 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4471 (by decide) v hb
mask_input "4471|37778931862974341578760|194638274443064161958100992"
def inputClause4472 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,true),(87,true)]
theorem inputList4472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4472 (by decide) v hb
mask_input "4472|37778931862974341578752|194638274443064161958101000"
def inputClause4473 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4473 (by decide) v hb
mask_input "4473|1217485108882010275848|194674835889818254289403904"
def inputClause4474 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4474 (by decide) v hb
mask_input "4474|1217485108882010275840|194674835889818254289403912"
def inputClause4475 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4475 (by decide) v hb
mask_input "4475|1180591620734591172616|194674872783306401708507136"
def inputClause4476 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4476 (by decide) v hb
mask_input "4476|1180591620734591172608|194674872783306401708507144"
def inputClause4477 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4477 (by decide) v hb
mask_input "4477|36893488164598972424|194676016481438971700707328"
def inputClause4478 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4478 (by decide) v hb
mask_input "4478|36893488164598972416|194676016481438971700707336"
def inputClause4479 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4479 (by decide) v hb
mask_input "4479|17179869192|194676053374927119119810560"
def inputClause4480 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem inputList4480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4480 (by decide) v hb
mask_input "4480|17179869184|194676053374927119119810568"
def inputClause4481 : CNF.NClause := [(35,true),(4,false),(63,false),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4481 (by decide) v hb
mask_input "4481|164725892026736180551745552|34359738368"
def inputClause4482 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4482 (by decide) v hb
mask_input "4482|164725892026736214911483904|16"
def inputClause4483 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4483 (by decide) v hb
mask_input "4483|164725882803364178056708112|9223372036854775808"
end Percolation.MaskChain
