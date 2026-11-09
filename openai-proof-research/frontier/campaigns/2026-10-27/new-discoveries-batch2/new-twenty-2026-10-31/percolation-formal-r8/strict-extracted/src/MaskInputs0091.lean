import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5216 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5216 (by decide) v hb
mask_input "5216|4835703278459616210452480|311941239911619679796331008"
def inputClause5217 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5217 (by decide) v hb
mask_input "5217|2456230090275710583177728|314320713099803585423605760"
def inputClause5218 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5218 (by decide) v hb
mask_input "5218|2456230090275710583177216|314320713099803585423606272"
def inputClause5219 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5219 (by decide) v hb
mask_input "5219|2456220866903673728401920|314320722323175622278381568"
def inputClause5220 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5220 (by decide) v hb
mask_input "5220|2456220866903673728401408|314320722323175622278382080"
def inputClause5221 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5221 (by decide) v hb
mask_input "5221|2455639794465351877526016|314321303395613944129257472"
def inputClause5222 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5222 (by decide) v hb
mask_input "5222|2455639794465351877525504|314321303395613944129257984"
def inputClause5223 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5223 (by decide) v hb
mask_input "5223|2455630571093315022750208|314321312618985980984033280"
def inputClause5224 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,true),(88,true)]
theorem inputList5224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5224 (by decide) v hb
mask_input "5224|2455630571093315022749696|314321312618985980984033792"
def inputClause5225 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5225 (by decide) v hb
mask_input "5225|2418451158412753421468160|314358492031666542585315328"
def inputClause5226 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5226 (by decide) v hb
mask_input "5226|2418451158412753421467648|314358492031666542585315840"
def inputClause5227 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5227 (by decide) v hb
mask_input "5227|2418441935040716566692352|314358501255038579440091136"
def inputClause5228 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5228 (by decide) v hb
mask_input "5228|2418441935040716566691840|314358501255038579440091648"
def inputClause5229 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5229 (by decide) v hb
mask_input "5229|2417860862602394715816448|314359082327476901290967040"
def inputClause5230 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5230 (by decide) v hb
mask_input "5230|2417860862602394715815936|314359082327476901290967552"
def inputClause5231 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5231 (by decide) v hb
mask_input "5231|2417851639230357861040640|314359091550848938145742848"
def inputClause5232 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,true),(88,true)]
theorem inputList5232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5232 (by decide) v hb
mask_input "5232|2417851639230357861040128|314359091550848938145743360"
def inputClause5233 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,true),(88,true)]
theorem inputList5233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5233 (by decide) v hb
mask_input "5233|38378451046452233765376|316738564739032843773018112"
def inputClause5234 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,true),(88,true)]
theorem inputList5234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5234 (by decide) v hb
mask_input "5234|38378451046452233764864|316738564739032843773018624"
def inputClause5236 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,true),(88,true)]
theorem inputList5236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5236 (by decide) v hb
mask_input "5236|38369227674415378989056|316738573962404880627794432"
def inputClause5237 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,true),(88,true)]
theorem inputList5237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5237 (by decide) v hb
mask_input "5237|37788155236093528113664|316739155034843202478669824"
def inputClause5238 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,true),(88,true)]
theorem inputList5238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5238 (by decide) v hb
mask_input "5238|37788155236093528113152|316739155034843202478670336"
def inputClause5240 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,true),(88,true)]
theorem inputList5240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5240 (by decide) v hb
mask_input "5240|37778931864056673337344|316739164258215239333446144"
def inputClause5242 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,true),(88,true)]
theorem inputList5242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5242 (by decide) v hb
mask_input "5242|599519183495072055296|316776343670895800934728192"
def inputClause5244 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,true),(88,true)]
theorem inputList5244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5244 (by decide) v hb
mask_input "5244|590295811458217279488|316776352894267837789504000"
def inputClause5245 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,true),(88,true)]
theorem inputList5245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5245 (by decide) v hb
mask_input "5245|9223373136366404096|316776933966706159640379392"
def inputClause5246 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,true),(88,true)]
theorem inputList5246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5246 (by decide) v hb
mask_input "5246|9223373136366403584|316776933966706159640379904"
def inputClause5248 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,true),(88,true)]
theorem inputList5248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5248 (by decide) v hb
mask_input "5248|1099511627776|316776943190078196495155712"
def inputClause5634 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5634 (by decide) v hb
mask_input "5634|329137174833312836886724608|8192"
def inputClause5650 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5650 (by decide) v hb
mask_input "5650|328834943378409179593048064|302231454903657293684736"
def inputClause5666 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5666 (by decide) v hb
mask_input "5666|309794361719478770091425792|19342813113834066795307008"
def inputClause5682 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5682 (by decide) v hb
mask_input "5682|309492130264575112797749248|19645044568737724088983552"
def inputClause5714 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inputList5714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5714 (by decide) v hb
mask_input "5714|19349933557064110868267008|309787241276248726018465792"
def inputClause5730 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inputList5730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5730 (by decide) v hb
mask_input "5730|309351898133701366644736|328827822935179135520088064"
def inputClause5746 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5746 (by decide) v hb
mask_input "5746|7120443230044072968192|329130054390082792813764608"
def inputClause5762 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5762 (by decide) v hb
mask_input "5762|696951647189344527501492224|16384"
def inputClause5766 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5766 (by decide) v hb
mask_input "5766|696950466597723810090188800|1180591620717411319808"
def inputClause5774 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5774 (by decide) v hb
mask_input "5774|696945744231240940444975104|5902958103587056533504"
def inputClause5782 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5782 (by decide) v hb
mask_input "5782|696346003687916495502835712|605643501428031998672896"
def inputClause5790 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5790 (by decide) v hb
mask_input "5790|696341281321433625857622016|610365867910901643886592"
end Percolation.MaskChain
