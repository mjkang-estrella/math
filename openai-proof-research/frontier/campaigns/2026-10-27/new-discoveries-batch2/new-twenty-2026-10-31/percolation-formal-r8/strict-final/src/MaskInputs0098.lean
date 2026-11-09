import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7056 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7056 (by decide) v hb
mask_input "7056|2496431817540238042787217408|75714661050540871385088"
def inputClause7057 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7057 (by decide) v hb
mask_input "7057|2495298606381673954483896320|1208925819614629174706176"
def inputClause7058 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7058 (by decide) v hb
mask_input "7058|2495298606381673954467119104|1208925819614629191483392"
def inputClause7059 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7059 (by decide) v hb
mask_input "7059|2495298597158301917629120512|1208935042986666029481984"
def inputClause7060 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7060 (by decide) v hb
mask_input "7060|2495298597158301917612343296|1208935042986666046259200"
def inputClause7061 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7061 (by decide) v hb
mask_input "7061|2495298458807721364807483392|1209073393567218851119104"
def inputClause7062 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7062 (by decide) v hb
mask_input "7062|2495298458807721364790706176|1209073393567218867896320"
def inputClause7063 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7063 (by decide) v hb
mask_input "7063|2495298449584349327952707584|1209082616939255705894912"
def inputClause7064 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inputList7064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7064 (by decide) v hb
mask_input "7064|2495298449584349327935930368|1209082616939255722672128"
def inputClause7065 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7065 (by decide) v hb
mask_input "7065|2495223048517948040160477184|1284483683340543498125312"
def inputClause7066 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7066 (by decide) v hb
mask_input "7066|2495223048517948040143699968|1284483683340543514902528"
def inputClause7067 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7067 (by decide) v hb
mask_input "7067|2495223039294576003305701376|1284492906712580352901120"
def inputClause7068 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7068 (by decide) v hb
mask_input "7068|2495223039294576003288924160|1284492906712580369678336"
def inputClause7170 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,false),(92,false)]
theorem inputList7170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7170 (by decide) v hb
mask_input "7170|4951760300175845264883449856|33554432"
def inputClause7172 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,false),(92,false)]
theorem inputList7172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7172 (by decide) v hb
mask_input "7172|4951760295564159246456061952|4611686018460942336"
def inputClause7174 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,false),(92,false)]
theorem inputList7174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7174 (by decide) v hb
mask_input "7174|4951760290952473228028674048|9223372036888330240"
def inputClause7176 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,false),(92,false)]
theorem inputList7176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7176 (by decide) v hb
mask_input "7176|4951760286340787209601286144|13835058055315718144"
def inputClause7178 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,false),(92,false)]
theorem inputList7178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7178 (by decide) v hb
mask_input "7178|4951760281729101191173898240|18446744073743106048"
def inputClause7180 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,false),(92,false)]
theorem inputList7180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7180 (by decide) v hb
mask_input "7180|4951760277117415172746510336|23058430092170493952"
def inputClause7182 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,false),(92,false)]
theorem inputList7182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7182 (by decide) v hb
mask_input "7182|4951760272505729154319122432|27670116110597881856"
def inputClause7184 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,false),(92,false)]
theorem inputList7184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7184 (by decide) v hb
mask_input "7184|4951760267894043135891734528|32281802129025269760"
def inputClause7186 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,false),(92,false)]
theorem inputList7186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7186 (by decide) v hb
mask_input "7186|4951760263282357117464346624|36893488147452657664"
def inputClause7188 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,false),(92,false)]
theorem inputList7188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7188 (by decide) v hb
mask_input "7188|4951760258670671099036958720|41505174165880045568"
def inputClause7190 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,false),(92,false)]
theorem inputList7190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7190 (by decide) v hb
mask_input "7190|4951760254058985080609570816|46116860184307433472"
def inputClause7192 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,false),(92,false)]
theorem inputList7192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7192 (by decide) v hb
mask_input "7192|4951760249447299062182182912|50728546202734821376"
def inputClause7194 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,false),(92,false)]
theorem inputList7194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7194 (by decide) v hb
mask_input "7194|4951760244835613043754795008|55340232221162209280"
def inputClause7196 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,false),(92,false)]
theorem inputList7196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7196 (by decide) v hb
mask_input "7196|4951760240223927025327407104|59951918239589597184"
def inputClause7198 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,false),(92,false)]
theorem inputList7198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7198 (by decide) v hb
mask_input "7198|4951760235612241006900019200|64563604258016985088"
def inputClause7200 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,false),(92,false)]
theorem inputList7200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7200 (by decide) v hb
mask_input "7200|4951760231000554988472631296|69175290276444372992"
def inputClause7202 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,true),(92,false)]
theorem inputList7202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7202 (by decide) v hb
mask_input "7202|4951760226388868970045243392|73786976294871760896"
def inputClause7204 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,true),(92,false)]
theorem inputList7204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7204 (by decide) v hb
mask_input "7204|4951760221777182951617855488|78398662313299148800"
def inputClause7206 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,true),(92,false)]
theorem inputList7206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7206 (by decide) v hb
mask_input "7206|4951760217165496933190467584|83010348331726536704"
def inputClause7208 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,true),(92,false)]
theorem inputList7208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7208 (by decide) v hb
mask_input "7208|4951760212553810914763079680|87622034350153924608"
def inputClause7210 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,true),(92,false)]
theorem inputList7210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7210 (by decide) v hb
mask_input "7210|4951760207942124896335691776|92233720368581312512"
def inputClause7212 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,true),(92,false)]
theorem inputList7212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7212 (by decide) v hb
mask_input "7212|4951760203330438877908303872|96845406387008700416"
def inputClause7214 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,true),(92,false)]
theorem inputList7214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7214 (by decide) v hb
mask_input "7214|4951760198718752859480915968|101457092405436088320"
def inputClause7216 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,true),(92,false)]
theorem inputList7216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7216 (by decide) v hb
mask_input "7216|4951760194107066841053528064|106068778423863476224"
def inputClause7218 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,true),(92,false)]
theorem inputList7218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7218 (by decide) v hb
mask_input "7218|4951760189495380822626140160|110680464442290864128"
def inputClause7220 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,true),(92,false)]
theorem inputList7220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7220 (by decide) v hb
mask_input "7220|4951760184883694804198752256|115292150460718252032"
def inputClause7222 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,true),(92,false)]
theorem inputList7222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7222 (by decide) v hb
mask_input "7222|4951760180272008785771364352|119903836479145639936"
end Percolation.MaskChain
