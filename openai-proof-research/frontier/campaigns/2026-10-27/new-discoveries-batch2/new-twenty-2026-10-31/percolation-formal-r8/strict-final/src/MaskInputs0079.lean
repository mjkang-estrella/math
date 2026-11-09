import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4072 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,true),(92,true)]
theorem inputList4072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4072 (by decide) v hb
mask_input "4072|1856910058928070414496169984|7891867750444299252481916929"
def inputClause4074 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,true),(92,true)]
theorem inputList4074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4074 (by decide) v hb
mask_input "4074|1702167554017397880133779456|8046610255354971786844307457"
def inputClause4076 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,true),(92,true)]
theorem inputList4076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4076 (by decide) v hb
mask_input "4076|1547425049106725345771388928|8201352760265644321206697985"
def inputClause4078 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,true),(92,true)]
theorem inputList4078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4078 (by decide) v hb
mask_input "4078|1392682544196052811408998400|8356095265176316855569088513"
def inputClause4080 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,true),(92,true)]
theorem inputList4080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4080 (by decide) v hb
mask_input "4080|1237940039285380277046607872|8510837770086989389931479041"
def inputClause4082 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,true),(92,true)]
theorem inputList4082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4082 (by decide) v hb
mask_input "4082|1083197534374707742684217344|8665580274997661924293869569"
def inputClause4084 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,true),(92,true)]
theorem inputList4084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4084 (by decide) v hb
mask_input "4084|928455029464035208321826816|8820322779908334458656260097"
def inputClause4086 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,true),(92,true)]
theorem inputList4086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4086 (by decide) v hb
mask_input "4086|773712524553362673959436288|8975065284819006993018650625"
def inputClause4088 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,true),(92,true)]
theorem inputList4088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4088 (by decide) v hb
mask_input "4088|618970019642690139597045760|9129807789729679527381041153"
def inputClause4090 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,true),(92,true)]
theorem inputList4090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4090 (by decide) v hb
mask_input "4090|464227514732017605234655232|9284550294640352061743431681"
def inputClause4092 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,true),(92,true)]
theorem inputList4092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4092 (by decide) v hb
mask_input "4092|309485009821345070872264704|9439292799551024596105822209"
def inputClause4094 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,true),(92,true)]
theorem inputList4094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4094 (by decide) v hb
mask_input "4094|154742504910672536509874176|9594035304461697130468212737"
def inputClause4096 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,true),(92,true)]
theorem inputList4096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4096 (by decide) v hb
mask_input "4096|2147483648|9748777809372369664830603265"
def inputClause4226 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4226 (by decide) v hb
mask_input "4226|174709279142799835331035136|4"
def inputClause4228 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4228 (by decide) v hb
mask_input "4228|174709260696055761621483520|18446744073709551620"
def inputClause4292 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,false),(87,true)]
theorem inputList4292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4292 (by decide) v hb
mask_input "4292|19966755785383227259092992|154742523357416608071942148"
def inputClause4484 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4484 (by decide) v hb
mask_input "4484|164725882803364178056708096|9223372036854775824"
def inputClause4548 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4548 (by decide) v hb
mask_input "4548|9983377892691643694317568|154742514134044571217166352"
def inputClause4610 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4610 (by decide) v hb
mask_input "4610|5101666958773735185979539456|32"
def inputClause4611 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4611 (by decide) v hb
mask_input "4611|5096831255495276669280714784|4835703278458516698824704"
def inputClause4612 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4612 (by decide) v hb
mask_input "4612|5096831255495276669280714752|4835703278458516698824736"
def inputClause4613 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4613 (by decide) v hb
mask_input "4613|5091995552216818152581890080|9671406556917033397649408"
def inputClause4614 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4614 (by decide) v hb
mask_input "4614|5091995552216818152581890048|9671406556917033397649440"
def inputClause4615 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4615 (by decide) v hb
mask_input "4615|5087159848938359635883065376|14507109835375550096474112"
def inputClause4616 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4616 (by decide) v hb
mask_input "4616|5087159848938359635883065344|14507109835375550096474144"
def inputClause4617 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4617 (by decide) v hb
mask_input "4617|5082324145659901119184240672|19342813113834066795298816"
def inputClause4618 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4618 (by decide) v hb
mask_input "4618|5082324145659901119184240640|19342813113834066795298848"
def inputClause4619 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4619 (by decide) v hb
mask_input "4619|5077488442381442602485415968|24178516392292583494123520"
def inputClause4620 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4620 (by decide) v hb
mask_input "4620|5077488442381442602485415936|24178516392292583494123552"
def inputClause4621 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4621 (by decide) v hb
mask_input "4621|5072652739102984085786591264|29014219670751100192948224"
def inputClause4622 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4622 (by decide) v hb
mask_input "4622|5072652739102984085786591232|29014219670751100192948256"
def inputClause4623 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4623 (by decide) v hb
mask_input "4623|5067817035824525569087766560|33849922949209616891772928"
def inputClause4624 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,false),(92,false)]
theorem inputList4624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4624 (by decide) v hb
mask_input "4624|5067817035824525569087766528|33849922949209616891772960"
def inputClause4625 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4625 (by decide) v hb
mask_input "4625|5062981332546067052388941856|38685626227668133590597632"
def inputClause4626 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4626 (by decide) v hb
mask_input "4626|5062981332546067052388941824|38685626227668133590597664"
def inputClause4627 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4627 (by decide) v hb
mask_input "4627|5058145629267608535690117152|43521329506126650289422336"
def inputClause4628 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4628 (by decide) v hb
mask_input "4628|5058145629267608535690117120|43521329506126650289422368"
def inputClause4629 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4629 (by decide) v hb
mask_input "4629|5053309925989150018991292448|48357032784585166988247040"
def inputClause4630 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4630 (by decide) v hb
mask_input "4630|5053309925989150018991292416|48357032784585166988247072"
def inputClause4631 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4631 (by decide) v hb
mask_input "4631|5048474222710691502292467744|53192736063043683687071744"
end Percolation.MaskChain
