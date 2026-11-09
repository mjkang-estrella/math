import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4363 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4363 (by decide) v hb
mask_input "4363|194638237549576031718866952|37815825351104580812800"
def inputClause4364 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4364 (by decide) v hb
mask_input "4364|194638237549576031718866944|37815825351104580812808"
def inputClause4365 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4365 (by decide) v hb
mask_input "4365|194637093851443461726666760|38959523483674573012992"
def inputClause4366 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4366 (by decide) v hb
mask_input "4366|194637093851443461726666752|38959523483674573013000"
def inputClause4367 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4367 (by decide) v hb
mask_input "4367|194637056957955314307563528|38996416971821992116224"
def inputClause4368 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem inputList4368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4368 (by decide) v hb
mask_input "4368|194637056957955314307563520|38996416971821992116232"
def inputClause4369 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4369 (by decide) v hb
mask_input "4369|193467127555312507124973576|1208925819614629174706176"
def inputClause4370 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4370 (by decide) v hb
mask_input "4370|193467127555312507124973568|1208925819614629174706184"
def inputClause4371 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4371 (by decide) v hb
mask_input "4371|193467090661824359705870344|1208962713102776593809408"
def inputClause4372 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4372 (by decide) v hb
mask_input "4372|193467090661824359705870336|1208962713102776593809416"
def inputClause4373 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4373 (by decide) v hb
mask_input "4373|193465946963691789713670152|1210106411235346586009600"
def inputClause4374 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4374 (by decide) v hb
mask_input "4374|193465946963691789713670144|1210106411235346586009608"
def inputClause4375 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4375 (by decide) v hb
mask_input "4375|193465910070203642294566920|1210143304723494005112832"
def inputClause4376 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,false),(87,false)]
theorem inputList4376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4376 (by decide) v hb
mask_input "4376|193465910070203642294566912|1210143304723494005112840"
def inputClause4377 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4377 (by decide) v hb
mask_input "4377|193429348623449549963264008|1246704751477586336415744"
def inputClause4378 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4378 (by decide) v hb
mask_input "4378|193429348623449549963264000|1246704751477586336415752"
def inputClause4379 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4379 (by decide) v hb
mask_input "4379|193429311729961402544160776|1246741644965733755518976"
def inputClause4380 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4380 (by decide) v hb
mask_input "4380|193429311729961402544160768|1246741644965733755518984"
def inputClause4381 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4381 (by decide) v hb
mask_input "4381|193428168031828832551960584|1247885343098303747719168"
def inputClause4382 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4382 (by decide) v hb
mask_input "4382|193428168031828832551960576|1247885343098303747719176"
def inputClause4383 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4383 (by decide) v hb
mask_input "4383|193428131138340685132857352|1247922236586451166822400"
def inputClause4384 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem inputList4384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4384 (by decide) v hb
mask_input "4384|193428131138340685132857344|1247922236586451166822408"
def inputClause4385 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4385 (by decide) v hb
mask_input "4385|155990427147259002709082120|38685626227668133590597632"
def inputClause4386 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4386 (by decide) v hb
mask_input "4386|155990427147259002709082112|38685626227668133590597640"
def inputClause4387 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4387 (by decide) v hb
mask_input "4387|155990390253770855289978888|38685663121156281009700864"
def inputClause4388 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4388 (by decide) v hb
mask_input "4388|155990390253770855289978880|38685663121156281009700872"
def inputClause4389 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4389 (by decide) v hb
mask_input "4389|155989246555638285297778696|38686806819288851001901056"
def inputClause4390 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4390 (by decide) v hb
mask_input "4390|155989246555638285297778688|38686806819288851001901064"
def inputClause4391 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4391 (by decide) v hb
mask_input "4391|155989209662150137878675464|38686843712776998421004288"
def inputClause4392 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem inputList4392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4392 (by decide) v hb
mask_input "4392|155989209662150137878675456|38686843712776998421004296"
def inputClause4393 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4393 (by decide) v hb
mask_input "4393|155952648215396045547372552|38723405159531090752307200"
def inputClause4394 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4394 (by decide) v hb
mask_input "4394|155952648215396045547372544|38723405159531090752307208"
def inputClause4395 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4395 (by decide) v hb
mask_input "4395|155952611321907898128269320|38723442053019238171410432"
def inputClause4396 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4396 (by decide) v hb
mask_input "4396|155952611321907898128269312|38723442053019238171410440"
def inputClause4397 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4397 (by decide) v hb
mask_input "4397|155951467623775328136069128|38724585751151808163610624"
def inputClause4398 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4398 (by decide) v hb
mask_input "4398|155951467623775328136069120|38724585751151808163610632"
def inputClause4399 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4399 (by decide) v hb
mask_input "4399|155951430730287180716965896|38724622644639955582713856"
def inputClause4400 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inputList4400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4400 (by decide) v hb
mask_input "4400|155951430730287180716965888|38724622644639955582713864"
def inputClause4401 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4401 (by decide) v hb
mask_input "4401|154781501327644373534375944|39894552047282762765303808"
def inputClause4402 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4402 (by decide) v hb
mask_input "4402|154781501327644373534375936|39894552047282762765303816"
end Percolation.MaskChain
