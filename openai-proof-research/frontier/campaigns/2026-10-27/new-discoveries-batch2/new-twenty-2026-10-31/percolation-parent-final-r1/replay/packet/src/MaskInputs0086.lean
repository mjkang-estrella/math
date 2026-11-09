import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5009 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5009 (by decide) v hb
mask_input "5009|1242851632468958582449111296|604462909807314587353088"
def inputClause5010 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5010 (by decide) v hb
mask_input "5010|1242851632468958582449111040|604462909807314587353344"
def inputClause5011 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5011 (by decide) v hb
mask_input "5011|1242851595575470435030008064|604499803295462006456320"
def inputClause5012 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5012 (by decide) v hb
mask_input "5012|1242851595575470435030007808|604499803295462006456576"
def inputClause5013 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5013 (by decide) v hb
mask_input "5013|1242851337321053403096285440|604758057712493940178944"
def inputClause5014 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5014 (by decide) v hb
mask_input "5014|1242851337321053403096285184|604758057712493940179200"
def inputClause5015 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5015 (by decide) v hb
mask_input "5015|1242851300427565255677182208|604794951200641359282176"
def inputClause5016 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inputList5016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5016 (by decide) v hb
mask_input "5016|1242851300427565255677181952|604794951200641359282432"
def inputClause5017 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5017 (by decide) v hb
mask_input "5017|1242776074605232668125692160|680020773533228910772224"
def inputClause5018 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5018 (by decide) v hb
mask_input "5018|1242776074605232668125691904|680020773533228910772480"
def inputClause5019 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5019 (by decide) v hb
mask_input "5019|1242776037711744520706588928|680057667021376329875456"
def inputClause5020 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5020 (by decide) v hb
mask_input "5020|1242776037711744520706588672|680057667021376329875712"
def inputClause5021 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5021 (by decide) v hb
mask_input "5021|1242775779457327488772866304|680315921438408263598080"
def inputClause5022 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5022 (by decide) v hb
mask_input "5022|1242775779457327488772866048|680315921438408263598336"
def inputClause5023 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5023 (by decide) v hb
mask_input "5023|1242775742563839341353763072|680352814926555682701312"
def inputClause5024 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inputList5024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5024 (by decide) v hb
mask_input "5024|1242775742563839341353762816|680352814926555682701568"
def inputClause5025 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5025 (by decide) v hb
mask_input "5025|1238620392100307380337639680|4835703278458516698824704"
def inputClause5026 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5026 (by decide) v hb
mask_input "5026|1238620392100307380337639424|4835703278458516698824960"
def inputClause5027 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5027 (by decide) v hb
mask_input "5027|1238620355206819232918536448|4835740171946664117927936"
def inputClause5028 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5028 (by decide) v hb
mask_input "5028|1238620355206819232918536192|4835740171946664117928192"
def inputClause5029 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5029 (by decide) v hb
mask_input "5029|1238620096952402200984813824|4835998426363696051650560"
def inputClause5030 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5030 (by decide) v hb
mask_input "5030|1238620096952402200984813568|4835998426363696051650816"
def inputClause5031 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5031 (by decide) v hb
mask_input "5031|1238620060058914053565710592|4836035319851843470753792"
def inputClause5032 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inputList5032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5032 (by decide) v hb
mask_input "5032|1238620060058914053565710336|4836035319851843470754048"
def inputClause5033 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5033 (by decide) v hb
mask_input "5033|1238544834236581466014220544|4911261142184431022243840"
def inputClause5034 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5034 (by decide) v hb
mask_input "5034|1238544834236581466014220288|4911261142184431022244096"
def inputClause5035 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5035 (by decide) v hb
mask_input "5035|1238544797343093318595117312|4911298035672578441347072"
def inputClause5036 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5036 (by decide) v hb
mask_input "5036|1238544797343093318595117056|4911298035672578441347328"
def inputClause5037 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5037 (by decide) v hb
mask_input "5037|1238544539088676286661394688|4911556290089610375069696"
def inputClause5038 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5038 (by decide) v hb
mask_input "5038|1238544539088676286661394432|4911556290089610375069952"
def inputClause5039 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5039 (by decide) v hb
mask_input "5039|1238544502195188139242291456|4911593183577757794172928"
def inputClause5040 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inputList5040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5040 (by decide) v hb
mask_input "5040|1238544502195188139242291200|4911593183577757794173184"
def inputClause5041 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inputList5041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5041 (by decide) v hb
mask_input "5041|1238015929190500065750286592|5440166188265831286177792"
def inputClause5042 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inputList5042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5042 (by decide) v hb
mask_input "5042|1238015929190500065750286336|5440166188265831286178048"
def inputClause5043 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inputList5043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5043 (by decide) v hb
mask_input "5043|1238015892297011918331183360|5440203081753978705281024"
def inputClause5044 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inputList5044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5044 (by decide) v hb
mask_input "5044|1238015892297011918331183104|5440203081753978705281280"
def inputClause5045 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,true),(90,false)]
theorem inputList5045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5045 (by decide) v hb
mask_input "5045|1238015634042594886397460736|5440461336171010639003648"
def inputClause5046 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,true),(90,false)]
theorem inputList5046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5046 (by decide) v hb
mask_input "5046|1238015634042594886397460480|5440461336171010639003904"
def inputClause5048 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,true),(90,false)]
theorem inputList5048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5048 (by decide) v hb
mask_input "5048|1238015597149106738978357248|5440498229659158058107136"
def inputClause5049 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5049 (by decide) v hb
mask_input "5049|1237940371326774151426867456|5515724051991745609596928"
end Percolation.MaskChain
