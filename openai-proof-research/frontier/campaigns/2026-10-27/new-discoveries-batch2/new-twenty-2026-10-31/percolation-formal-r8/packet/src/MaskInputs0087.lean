import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5050 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5050 (by decide) v hb
mask_input "5050|1237940371326774151426867200|5515724051991745609597184"
def inputClause5051 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5051 (by decide) v hb
mask_input "5051|1237940334433286004007764224|5515760945479893028700160"
def inputClause5052 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5052 (by decide) v hb
mask_input "5052|1237940334433286004007763968|5515760945479893028700416"
def inputClause5053 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5053 (by decide) v hb
mask_input "5053|1237940076178868972074041600|5516019199896924962422784"
def inputClause5054 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5054 (by decide) v hb
mask_input "5054|1237940076178868972074041344|5516019199896924962423040"
def inputClause5055 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5055 (by decide) v hb
mask_input "5055|1237940039285380824654938368|5516056093385072381526016"
def inputClause5056 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inputList5056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5056 (by decide) v hb
mask_input "5056|1237940039285380824654938112|5516056093385072381526272"
def inputClause5057 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5057 (by decide) v hb
mask_input "5057|5516056093385622137340160|1237940039285380274899124224"
def inputClause5058 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5058 (by decide) v hb
mask_input "5058|5516056093385622137339904|1237940039285380274899124480"
def inputClause5059 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5059 (by decide) v hb
mask_input "5059|5516019199897474718236928|1237940076178868422318227456"
def inputClause5060 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5060 (by decide) v hb
mask_input "5060|5516019199897474718236672|1237940076178868422318227712"
def inputClause5061 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5061 (by decide) v hb
mask_input "5061|5515760945480442784514304|1237940334433285454251950080"
def inputClause5062 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5062 (by decide) v hb
mask_input "5062|5515760945480442784514048|1237940334433285454251950336"
def inputClause5063 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5063 (by decide) v hb
mask_input "5063|5515724051992295365411072|1237940371326773601671053312"
def inputClause5064 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inputList5064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5064 (by decide) v hb
mask_input "5064|5515724051992295365410816|1237940371326773601671053568"
def inputClause5065 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5065 (by decide) v hb
mask_input "5065|5440498229659707813921024|1238015597149106189222543360"
def inputClause5066 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5066 (by decide) v hb
mask_input "5066|5440498229659707813920768|1238015597149106189222543616"
def inputClause5067 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5067 (by decide) v hb
mask_input "5067|5440461336171560394817792|1238015634042594336641646592"
def inputClause5068 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5068 (by decide) v hb
mask_input "5068|5440461336171560394817536|1238015634042594336641646848"
def inputClause5069 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5069 (by decide) v hb
mask_input "5069|5440203081754528461095168|1238015892297011368575369216"
def inputClause5070 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5070 (by decide) v hb
mask_input "5070|5440203081754528461094912|1238015892297011368575369472"
def inputClause5071 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5071 (by decide) v hb
mask_input "5071|5440166188266381041991936|1238015929190499515994472448"
def inputClause5072 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inputList5072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5072 (by decide) v hb
mask_input "5072|5440166188266381041991680|1238015929190499515994472704"
def inputClause5073 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inputList5073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5073 (by decide) v hb
mask_input "5073|4911593183578307549987072|1238544502195187589486477312"
def inputClause5074 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inputList5074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5074 (by decide) v hb
mask_input "5074|4911593183578307549986816|1238544502195187589486477568"
def inputClause5075 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inputList5075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5075 (by decide) v hb
mask_input "5075|4911556290090160130883840|1238544539088675736905580544"
def inputClause5076 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inputList5076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5076 (by decide) v hb
mask_input "5076|4911556290090160130883584|1238544539088675736905580800"
def inputClause5077 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,false),(90,true)]
theorem inputList5077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5077 (by decide) v hb
mask_input "5077|4911298035673128197161216|1238544797343092768839303168"
def inputClause5078 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,false),(90,true)]
theorem inputList5078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5078 (by decide) v hb
mask_input "5078|4911298035673128197160960|1238544797343092768839303424"
def inputClause5080 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,false),(90,true)]
theorem inputList5080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5080 (by decide) v hb
mask_input "5080|4911261142184980778057728|1238544834236580916258406656"
def inputClause5081 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inputList5081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5081 (by decide) v hb
mask_input "5081|4836035319852393226567936|1238620060058913503809896448"
def inputClause5082 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inputList5082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5082 (by decide) v hb
mask_input "5082|4836035319852393226567680|1238620060058913503809896704"
def inputClause5083 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inputList5083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5083 (by decide) v hb
mask_input "5083|4835998426364245807464704|1238620096952401651228999680"
def inputClause5084 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inputList5084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5084 (by decide) v hb
mask_input "5084|4835998426364245807464448|1238620096952401651228999936"
def inputClause5085 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,false),(90,true)]
theorem inputList5085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5085 (by decide) v hb
mask_input "5085|4835740171947213873742080|1238620355206818683162722304"
def inputClause5086 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,false),(90,true)]
theorem inputList5086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5086 (by decide) v hb
mask_input "5086|4835740171947213873741824|1238620355206818683162722560"
def inputClause5088 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,false),(90,true)]
theorem inputList5088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5088 (by decide) v hb
mask_input "5088|4835703278459066454638592|1238620392100306830581825792"
def inputClause5089 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5089 (by decide) v hb
mask_input "5089|680352814927105438515456|1242775742563838791597948928"
def inputClause5090 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5090 (by decide) v hb
mask_input "5090|680352814927105438515200|1242775742563838791597949184"
def inputClause5091 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5091 (by decide) v hb
mask_input "5091|680315921438958019412224|1242775779457326939017052160"
end Percolation.MaskChain
