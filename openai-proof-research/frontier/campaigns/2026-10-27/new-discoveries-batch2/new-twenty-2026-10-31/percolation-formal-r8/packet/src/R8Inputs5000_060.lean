import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7165 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,true),(91,true)]
theorem inputList7165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7165 (by decide) v hb
mask_input "7165|9259400833890516992|2496507522941887749768085504"
def inputClause7166 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,true),(91,true)]
theorem inputList7166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7166 (by decide) v hb
mask_input "7166|9259400833873739776|2496507522941887749784862720"
def inputClause7168 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,true),(91,true)]
theorem inputList7168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7168 (by decide) v hb
mask_input "7168|36028797018963968|2496507532165259786639638528"
def inputClause7297 : CNF.NClause := [(57,true),(26,false),(62,false),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7297 (by decide) v hb
mask_input "7297|2486196092764275308262064128|144115188075855872"
def inputClause7298 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7298 (by decide) v hb
mask_input "7298|2486196092908390496270811136|67108864"
def inputClause7299 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7299 (by decide) v hb
mask_input "7299|2486196088296704477910532096|4611686018427387904"
def inputClause7301 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7301 (by decide) v hb
mask_input "7301|2486193731725149061515313152|2361183241434822606848"
def inputClause7302 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7302 (by decide) v hb
mask_input "7302|2486193731725149061448204288|2361183241434889715712"
def inputClause7303 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7303 (by decide) v hb
mask_input "7303|2486193727113463043087925248|2365794927453249994752"
def inputClause7304 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7304 (by decide) v hb
mask_input "7304|2486193727113463043020816384|2365794927453317103616"
def inputClause7305 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7305 (by decide) v hb
mask_input "7305|2486158313976527539176210432|37778931862957161709568"
def inputClause7306 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7306 (by decide) v hb
mask_input "7306|2486158313976527539109101568|37778931862957228818432"
def inputClause7307 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7307 (by decide) v hb
mask_input "7307|2486158309364841520748822528|37783543548975589097472"
def inputClause7309 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7309 (by decide) v hb
mask_input "7309|2486155952793286104353603584|40140115104391984316416"
def inputClause7310 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7310 (by decide) v hb
mask_input "7310|2486155952793286104286494720|40140115104392051425280"
def inputClause7311 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7311 (by decide) v hb
mask_input "7311|2486155948181600085926215680|40144726790410411704320"
def inputClause7312 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7312 (by decide) v hb
mask_input "7312|2486155948181600085859106816|40144726790410478813184"
def inputClause7313 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7313 (by decide) v hb
mask_input "7313|2485591629998583181750566912|604462909807314587353088"
def inputClause7314 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7314 (by decide) v hb
mask_input "7314|2485591629998583181683458048|604462909807314654461952"
def inputClause7315 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7315 (by decide) v hb
mask_input "7315|2485591625386897163323179008|604467521493333014740992"
def inputClause7317 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7317 (by decide) v hb
mask_input "7317|2485589268815341746927960064|606824093048749409959936"
def inputClause7318 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7318 (by decide) v hb
mask_input "7318|2485589268815341746860851200|606824093048749477068800"
def inputClause7319 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7319 (by decide) v hb
mask_input "7319|2485589264203655728500572160|606828704734767837347840"
def inputClause7320 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7320 (by decide) v hb
mask_input "7320|2485589264203655728433463296|606828704734767904456704"
def inputClause7321 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inputList7321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7321 (by decide) v hb
mask_input "7321|2485553851066720224588857344|642241841670271749062656"
def inputClause7322 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inputList7322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7322 (by decide) v hb
mask_input "7322|2485553851066720224521748480|642241841670271816171520"
def inputClause7323 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inputList7323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7323 (by decide) v hb
mask_input "7323|2485553846455034206161469440|642246453356290176450560"
def inputClause7325 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,true),(83,false),(91,false)]
theorem inputList7325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7325 (by decide) v hb
mask_input "7325|2485551489883478789766250496|644603024911706571669504"
def inputClause7326 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,false),(91,false)]
theorem inputList7326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7326 (by decide) v hb
mask_input "7326|2485551489883478789699141632|644603024911706638778368"
def inputClause7328 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,false),(91,false)]
theorem inputList7328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7328 (by decide) v hb
mask_input "7328|2485551485271792771271753728|644607636597725066166272"
def inputClause7329 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7329 (by decide) v hb
mask_input "7329|2476524686351473462940270592|9671406556917033397649408"
def inputClause7330 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7330 (by decide) v hb
mask_input "7330|2476524686351473462873161728|9671406556917033464758272"
def inputClause7331 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7331 (by decide) v hb
mask_input "7331|2476524681739787444512882688|9671411168603051825037312"
def inputClause7333 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7333 (by decide) v hb
mask_input "7333|2476522325168232028117663744|9673767740158468220256256"
def inputClause7334 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7334 (by decide) v hb
mask_input "7334|2476522325168232028050554880|9673767740158468287365120"
def inputClause7335 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7335 (by decide) v hb
mask_input "7335|2476522320556546009690275840|9673772351844486647644160"
def inputClause7336 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7336 (by decide) v hb
mask_input "7336|2476522320556546009623166976|9673772351844486714753024"
def inputClause7338 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inputList7338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7338 (by decide) v hb
mask_input "7338|2476486907419610505711452160|9709185488779990626467840"
def inputClause7339 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inputList7339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7339 (by decide) v hb
mask_input "7339|2476486902807924487351173120|9709190100466008986746880"
def inputClause7341 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inputList7341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7341 (by decide) v hb
mask_input "7341|2476484546236369070955954176|9711546672021425381965824"
end Percolation.MaskChain
