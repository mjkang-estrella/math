import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5692 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5692 (by decide) v hb
mask_input "5692|309487371004604095733432320|19649803828708741153300480"
def inputClause5693 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5693 (by decide) v hb
mask_input "5693|309485046714850808329936896|19652128118462028556795904"
def inputClause5694 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5694 (by decide) v hb
mask_input "5694|309485046714850808329928704|19652128118462028556804096"
def inputClause5695 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5695 (by decide) v hb
mask_input "5695|309485009821362660910833664|19652165011950175975899136"
def inputClause5696 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5696 (by decide) v hb
mask_input "5696|309485009821362660910825472|19652165011950175975907328"
def inputClause5697 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5697 (by decide) v hb
mask_input "5697|19652165011967768161951744|309485009821345068724781056"
def inputClause5698 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5698 (by decide) v hb
mask_input "5698|19652165011967768161943552|309485009821345068724789248"
def inputClause5699 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5699 (by decide) v hb
mask_input "5699|19652128118479620742848512|309485046714833216143884288"
def inputClause5700 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5700 (by decide) v hb
mask_input "5700|19652128118479620742840320|309485046714833216143892480"
def inputClause5701 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5701 (by decide) v hb
mask_input "5701|19649803828726333339344896|309487371004586503547387904"
def inputClause5702 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5702 (by decide) v hb
mask_input "5702|19649803828726333339336704|309487371004586503547396096"
def inputClause5703 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5703 (by decide) v hb
mask_input "5703|19649766935238185920241664|309487407898074650966491136"
def inputClause5704 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inputList5704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5704 (by decide) v hb
mask_input "5704|19649766935238185920233472|309487407898074650966499328"
def inputClause5705 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5705 (by decide) v hb
mask_input "5705|19647442645484898516738048|309489732187827938369994752"
def inputClause5706 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5706 (by decide) v hb
mask_input "5706|19647442645484898516729856|309489732187827938370002944"
def inputClause5707 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5707 (by decide) v hb
mask_input "5707|19647405751996751097634816|309489769081316085789097984"
def inputClause5708 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5708 (by decide) v hb
mask_input "5708|19647405751996751097626624|309489769081316085789106176"
def inputClause5709 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5709 (by decide) v hb
mask_input "5709|19645081462243463694131200|309492093371069373192601600"
def inputClause5710 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5710 (by decide) v hb
mask_input "5710|19645081462243463694123008|309492093371069373192609792"
def inputClause5711 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5711 (by decide) v hb
mask_input "5711|19645044568755316275027968|309492130264557520611704832"
def inputClause5712 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inputList5712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5712 (by decide) v hb
mask_input "5712|19645044568755316275019776|309492130264557520611713024"
def inputClause5713 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5713 (by decide) v hb
mask_input "5713|19349933557064110868275200|309787241276248726018457600"
def inputClause5715 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5715 (by decide) v hb
mask_input "5715|19349896663575963449171968|309787278169736873437560832"
def inputClause5716 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5716 (by decide) v hb
mask_input "5716|19349896663575963449163776|309787278169736873437569024"
def inputClause5717 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5717 (by decide) v hb
mask_input "5717|19347572373822676045668352|309789602459490160841064448"
def inputClause5718 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5718 (by decide) v hb
mask_input "5718|19347572373822676045660160|309789602459490160841072640"
def inputClause5719 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5719 (by decide) v hb
mask_input "5719|19347535480334528626565120|309789639352978308260167680"
def inputClause5720 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5720 (by decide) v hb
mask_input "5720|19347535480334528626556928|309789639352978308260175872"
def inputClause5721 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5721 (by decide) v hb
mask_input "5721|19345211190581241223061504|309791963642731595663671296"
def inputClause5722 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5722 (by decide) v hb
mask_input "5722|19345211190581241223053312|309791963642731595663679488"
def inputClause5723 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5723 (by decide) v hb
mask_input "5723|19345174297093093803958272|309792000536219743082774528"
def inputClause5724 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5724 (by decide) v hb
mask_input "5724|19345174297093093803950080|309792000536219743082782720"
def inputClause5725 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5725 (by decide) v hb
mask_input "5725|19342850007339806400454656|309794324825973030486278144"
def inputClause5726 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5726 (by decide) v hb
mask_input "5726|19342850007339806400446464|309794324825973030486286336"
def inputClause5727 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5727 (by decide) v hb
mask_input "5727|19342813113851658981351424|309794361719461177905381376"
def inputClause5728 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inputList5728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5728 (by decide) v hb
mask_input "5728|19342813113851658981343232|309794361719461177905389568"
def inputClause5729 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inputList5729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5729 (by decide) v hb
mask_input "5729|309351898133701366652928|328827822935179135520079872"
def inputClause5731 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inputList5731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5731 (by decide) v hb
mask_input "5731|309315004645553947549696|328827859828667282939183104"
def inputClause5732 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inputList5732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5732 (by decide) v hb
mask_input "5732|309315004645553947541504|328827859828667282939191296"
def inputClause5733 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,true),(88,true)]
theorem inputList5733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5733 (by decide) v hb
mask_input "5733|306990714892266544046080|328830184118420570342686720"
end Percolation.MaskChain
