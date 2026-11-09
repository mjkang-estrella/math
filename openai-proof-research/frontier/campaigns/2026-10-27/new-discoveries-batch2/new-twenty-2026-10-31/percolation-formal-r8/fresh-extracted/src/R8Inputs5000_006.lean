import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4148 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inputList4148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4148 (by decide) v hb
mask_input "4148|154820423957639887803383808|79789177881541820368814082"
def inputClause4149 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,true),(87,false)]
theorem inputList4149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4149 (by decide) v hb
mask_input "4149|154818136561374747818983426|79791465277806960353214464"
def inputClause4150 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,true),(87,false)]
theorem inputList4150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4150 (by decide) v hb
mask_input "4150|154818136561374747818983424|79791465277806960353214466"
def inputClause4152 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,true),(87,false)]
theorem inputList4152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4152 (by decide) v hb
mask_input "4152|154818062774398452980776960|79791539064783255191420930"
def inputClause4153 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,true),(87,false)]
theorem inputList4153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4153 (by decide) v hb
mask_input "4153|154744939880890268318171138|79864661958291439854026752"
def inputClause4154 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,true),(87,false)]
theorem inputList4154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4154 (by decide) v hb
mask_input "4154|154744939880890268318171136|79864661958291439854026754"
def inputClause4157 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inputList4157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4157 (by decide) v hb
mask_input "4157|154742578697648833495564290|79867023141532874676633600"
def inputClause4158 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inputList4158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4158 (by decide) v hb
mask_input "4158|154742578697648833495564288|79867023141532874676633602"
def inputClause4159 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inputList4159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4159 (by decide) v hb
mask_input "4159|154742504910672538657357826|79867096928509169514840064"
def inputClause4160 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,true),(87,false)]
theorem inputList4160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4160 (by decide) v hb
mask_input "4160|154742504910672538657357824|79867096928509169514840066"
def inputClause4161 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4161 (by decide) v hb
mask_input "4161|79867096928509173809807362|154742504910672534362390528"
def inputClause4162 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4162 (by decide) v hb
mask_input "4162|79867096928509173809807360|154742504910672534362390530"
def inputClause4163 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4163 (by decide) v hb
mask_input "4163|79867023141532878971600898|154742578697648829200596992"
def inputClause4164 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4164 (by decide) v hb
mask_input "4164|79867023141532878971600896|154742578697648829200596994"
def inputClause4165 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4165 (by decide) v hb
mask_input "4165|79864735745267738987200514|154744866093913969184997376"
def inputClause4166 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4166 (by decide) v hb
mask_input "4166|79864735745267738987200512|154744866093913969184997378"
def inputClause4167 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4167 (by decide) v hb
mask_input "4167|79864661958291444148994050|154744939880890264023203840"
def inputClause4168 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,false),(87,true)]
theorem inputList4168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4168 (by decide) v hb
mask_input "4168|79864661958291444148994048|154744939880890264023203842"
def inputClause4169 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4169 (by decide) v hb
mask_input "4169|79791539064783259486388226|154818062774398448685809664"
def inputClause4170 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4170 (by decide) v hb
mask_input "4170|79791539064783259486388224|154818062774398448685809666"
def inputClause4171 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4171 (by decide) v hb
mask_input "4171|79791465277806964648181762|154818136561374743524016128"
def inputClause4172 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4172 (by decide) v hb
mask_input "4172|79791465277806964648181760|154818136561374743524016130"
def inputClause4173 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4173 (by decide) v hb
mask_input "4173|79789177881541824663781378|154820423957639883508416512"
def inputClause4174 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4174 (by decide) v hb
mask_input "4174|79789177881541824663781376|154820423957639883508416514"
def inputClause4175 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4175 (by decide) v hb
mask_input "4175|79789104094565529825574914|154820497744616178346622976"
def inputClause4176 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,false),(87,true)]
theorem inputList4176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4176 (by decide) v hb
mask_input "4176|79789104094565529825574912|154820497744616178346622978"
def inputClause4177 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4177 (by decide) v hb
mask_input "4177|77449245289279915460395010|157160356549901792711802880"
def inputClause4178 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4178 (by decide) v hb
mask_input "4178|77449245289279915460395008|157160356549901792711802882"
def inputClause4179 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4179 (by decide) v hb
mask_input "4179|77449171502303620622188546|157160430336878087550009344"
def inputClause4180 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4180 (by decide) v hb
mask_input "4180|77449171502303620622188544|157160430336878087550009346"
def inputClause4181 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4181 (by decide) v hb
mask_input "4181|77446884106038480637788162|157162717733143227534409728"
def inputClause4182 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4182 (by decide) v hb
mask_input "4182|77446884106038480637788160|157162717733143227534409730"
def inputClause4183 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4183 (by decide) v hb
mask_input "4183|77446810319062185799581698|157162791520119522372616192"
def inputClause4184 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,false),(87,true)]
theorem inputList4184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4184 (by decide) v hb
mask_input "4184|77446810319062185799581696|157162791520119522372616194"
def inputClause4185 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4185 (by decide) v hb
mask_input "4185|77373687425554001136975874|157235914413627707035222016"
def inputClause4186 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4186 (by decide) v hb
mask_input "4186|77373687425554001136975872|157235914413627707035222018"
def inputClause4187 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4187 (by decide) v hb
mask_input "4187|77373613638577706298769410|157235988200604001873428480"
def inputClause4188 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4188 (by decide) v hb
mask_input "4188|77373613638577706298769408|157235988200604001873428482"
def inputClause4189 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4189 (by decide) v hb
mask_input "4189|77371326242312566314369026|157238275596869141857828864"
def inputClause4190 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4190 (by decide) v hb
mask_input "4190|77371326242312566314369024|157238275596869141857828866"
end Percolation.MaskChain
