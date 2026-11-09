import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4979 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inputList4979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4979 (by decide) v hb
mask_input "4979|11805916207448990941312|625014667187507357032644608"
def inputClause4980 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inputList4980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4980 (by decide) v hb
mask_input "4980|11805916207448990941184|625014667187507357032644736"
def inputClause4981 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,true),(89,true)]
theorem inputList4981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4981 (by decide) v hb
mask_input "4981|9463179710087877886080|625017009924004718145699840"
def inputClause4982 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,true),(89,true)]
theorem inputList4982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4982 (by decide) v hb
mask_input "4982|9463179710087877885952|625017009924004718145699968"
def inputClause4984 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,true),(89,true)]
theorem inputList4984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4984 (by decide) v hb
mask_input "4984|9444732966014168334336|625017028370748791855251584"
def inputClause4985 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4985 (by decide) v hb
mask_input "4985|2379629985783410065536|625024093473729022613520384"
def inputClause4986 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4986 (by decide) v hb
mask_input "4986|2379629985783410065408|625024093473729022613520512"
def inputClause4987 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4987 (by decide) v hb
mask_input "4987|2361183241709700513920|625024111920473096323072000"
def inputClause4988 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4988 (by decide) v hb
mask_input "4988|2361183241709700513792|625024111920473096323072128"
def inputClause4989 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4989 (by decide) v hb
mask_input "4989|18446744348587458688|625026454656970457436127232"
def inputClause4990 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4990 (by decide) v hb
mask_input "4990|18446744348587458560|625026454656970457436127360"
def inputClause4991 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4991 (by decide) v hb
mask_input "4991|274877907072|625026473103714531145678848"
def inputClause4992 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inputList4992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4992 (by decide) v hb
mask_input "4992|274877906944|625026473103714531145678976"
def inputClause4993 : CNF.NClause := [(39,true),(8,false),(65,false),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inputList4993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause4993 (by decide) v hb
mask_input "4993|1243456095378765347280650496|549755813888"
def inputClause5121 : CNF.NClause := [(40,true),(9,false),(63,false),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5121 (by decide) v hb
mask_input "5121|316776943190078196495155712|1099511627776"
def inputClause5249 : CNF.NClause := [(41,true),(10,false),(72,false),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5249 (by decide) v hb
mask_input "5249|4951906550502490058598122496|2199023255552"
def inputClause5250 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5250 (by decide) v hb
mask_input "5250|4951906550502492257621377024|1024"
def inputClause5251 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5251 (by decide) v hb
mask_input "5251|4951901828136009387976164352|4722366482869645213696"
def inputClause5252 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5252 (by decide) v hb
mask_input "5252|4951901828136009387976163328|4722366482869645214720"
def inputClause5253 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5253 (by decide) v hb
mask_input "5253|4951897105769526518330950656|9444732965739290427392"
def inputClause5254 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5254 (by decide) v hb
mask_input "5254|4951897105769526518330949632|9444732965739290428416"
def inputClause5255 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5255 (by decide) v hb
mask_input "5255|4951892383403043648685736960|14167099448608935641088"
def inputClause5256 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,false),(92,false)]
theorem inputList5256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5256 (by decide) v hb
mask_input "5256|4951892383403043648685735936|14167099448608935642112"
def inputClause5257 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5257 (by decide) v hb
mask_input "5257|4951887661036560779040523264|18889465931478580854784"
def inputClause5258 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5258 (by decide) v hb
mask_input "5258|4951887661036560779040522240|18889465931478580855808"
def inputClause5259 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5259 (by decide) v hb
mask_input "5259|4951882938670077909395309568|23611832414348226068480"
def inputClause5260 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5260 (by decide) v hb
mask_input "5260|4951882938670077909395308544|23611832414348226069504"
def inputClause5261 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5261 (by decide) v hb
mask_input "5261|4951878216303595039750095872|28334198897217871282176"
def inputClause5262 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5262 (by decide) v hb
mask_input "5262|4951878216303595039750094848|28334198897217871283200"
def inputClause5263 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5263 (by decide) v hb
mask_input "5263|4951873493937112170104882176|33056565380087516495872"
def inputClause5264 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,false),(92,false)]
theorem inputList5264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5264 (by decide) v hb
mask_input "5264|4951873493937112170104881152|33056565380087516496896"
def inputClause5265 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5265 (by decide) v hb
mask_input "5265|4951868771570629300459668480|37778931862957161709568"
def inputClause5266 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5266 (by decide) v hb
mask_input "5266|4951868771570629300459667456|37778931862957161710592"
def inputClause5267 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5267 (by decide) v hb
mask_input "5267|4951864049204146430814454784|42501298345826806923264"
def inputClause5268 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5268 (by decide) v hb
mask_input "5268|4951864049204146430814453760|42501298345826806924288"
def inputClause5269 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5269 (by decide) v hb
mask_input "5269|4951859326837663561169241088|47223664828696452136960"
def inputClause5270 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5270 (by decide) v hb
mask_input "5270|4951859326837663561169240064|47223664828696452137984"
def inputClause5271 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5271 (by decide) v hb
mask_input "5271|4951854604471180691524027392|51946031311566097350656"
def inputClause5272 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inputList5272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5272 (by decide) v hb
mask_input "5272|4951854604471180691524026368|51946031311566097351680"
def inputClause5273 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem inputList5273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5273 (by decide) v hb
mask_input "5273|4951849882104697821878813696|56668397794435742564352"
end Percolation.MaskChain
