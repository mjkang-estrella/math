import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6240 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6240 (by decide) v hb
mask_input "6240|9671406557198508374360064|309712882450887602816024576"
def inputClause6241 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6241 (by decide) v hb
mask_input "6241|227872629824009067954176|319156416378262102122430464"
def inputClause6243 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6243 (by decide) v hb
mask_input "6243|227854183079935358402560|319156434825006175831982080"
def inputClause6244 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6244 (by decide) v hb
mask_input "6244|227854183079935358271488|319156434825006175832113152"
def inputClause6245 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6245 (by decide) v hb
mask_input "6245|226692038203291656650752|319157596969882819533733888"
def inputClause6246 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6246 (by decide) v hb
mask_input "6246|226692038203291656519680|319157596969882819533864960"
def inputClause6247 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6247 (by decide) v hb
mask_input "6247|226673591459217947099136|319157615416626893243285504"
def inputClause6248 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6248 (by decide) v hb
mask_input "6248|226673591459217946968064|319157615416626893243416576"
def inputClause6249 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,true),(88,true)]
theorem inputList6249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6249 (by decide) v hb
mask_input "6249|152314766098094744535040|319231974241988016445849600"
def inputClause6252 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,true),(88,true)]
theorem inputList6252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6252 (by decide) v hb
mask_input "6252|152296319354021034852352|319231992688732090155532288"
def inputClause6253 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,true),(88,true)]
theorem inputList6253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6253 (by decide) v hb
mask_input "6253|151134174477377333231616|319233154833608733857153024"
def inputClause6254 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,true),(88,true)]
theorem inputList6254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6254 (by decide) v hb
mask_input "6254|151134174477377333100544|319233154833608733857284096"
def inputClause6256 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,true),(88,true)]
theorem inputList6256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6256 (by decide) v hb
mask_input "6256|151115727733303623548928|319233173280352807566835712"
def inputClause6259 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,true),(88,true)]
theorem inputList6259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6259 (by decide) v hb
mask_input "6259|76738455628106711564288|319307550552458004478820352"
def inputClause6260 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,true),(88,true)]
theorem inputList6260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6260 (by decide) v hb
mask_input "6260|76738455628106711433216|319307550552458004478951424"
def inputClause6261 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inputList6261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6261 (by decide) v hb
mask_input "6261|75576310751463009812480|319308712697334648180572160"
def inputClause6262 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inputList6262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6262 (by decide) v hb
mask_input "6262|75576310751463009681408|319308712697334648180703232"
def inputClause6263 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inputList6263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6263 (by decide) v hb
mask_input "6263|75557864007389300260864|319308731144078721890123776"
def inputClause6264 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inputList6264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6264 (by decide) v hb
mask_input "6264|75557864007389300129792|319308731144078721890254848"
def inputClause6268 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,true),(88,true)]
theorem inputList6268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6268 (by decide) v hb
mask_input "6268|1180591902192388014080|319383108416183918802370560"
def inputClause6269 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,true),(88,true)]
theorem inputList6269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6269 (by decide) v hb
mask_input "6269|18447025548686393344|319384270561060562503991296"
def inputClause6270 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,true),(88,true)]
theorem inputList6270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6270 (by decide) v hb
mask_input "6270|18447025548686262272|319384270561060562504122368"
def inputClause6272 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,true),(88,true)]
theorem inputList6272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6272 (by decide) v hb
mask_input "6272|281474976710656|319384289007804636213673984"
def inputClause6273 : CNF.NClause := [(49,true),(18,false),(65,false),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6273 (by decide) v hb
mask_input "6273|2553412518675812891041726464|562949953421312"
def inputClause6275 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6275 (by decide) v hb
mask_input "6275|2553412481782887693576044544|36893488147419103232"
def inputClause6276 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6276 (by decide) v hb
mask_input "6276|2553412481782887693575782400|36893488147419365376"
def inputClause6277 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6277 (by decide) v hb
mask_input "6277|2553411928380565482289496064|590295810358705651712"
def inputClause6278 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6278 (by decide) v hb
mask_input "6278|2553411928380565482289233920|590295810358705913856"
def inputClause6279 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6279 (by decide) v hb
mask_input "6279|2553411891487077334870392832|627189298506124754944"
def inputClause6280 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6280 (by decide) v hb
mask_input "6280|2553411891487077334870130688|627189298506125017088"
def inputClause6281 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6281 (by decide) v hb
mask_input "6281|2553403073943410101704720384|9444732965739290427392"
def inputClause6282 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6282 (by decide) v hb
mask_input "6282|2553403073943410101704458240|9444732965739290689536"
def inputClause6283 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6283 (by decide) v hb
mask_input "6283|2553403037049921954285617152|9481626453886709530624"
def inputClause6284 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6284 (by decide) v hb
mask_input "6284|2553403037049921954285355008|9481626453886709792768"
def inputClause6285 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6285 (by decide) v hb
mask_input "6285|2553402483647599742999068672|10035028776097996079104"
def inputClause6286 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6286 (by decide) v hb
mask_input "6286|2553402483647599742998806528|10035028776097996341248"
def inputClause6287 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6287 (by decide) v hb
mask_input "6287|2553402446754111595579965440|10071922264245415182336"
def inputClause6288 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inputList6288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6288 (by decide) v hb
mask_input "6288|2553402446754111595579703296|10071922264245415444480"
def inputClause6291 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6291 (by decide) v hb
mask_input "6291|2553261366055435864929206272|151152620939976065941504"
def inputClause6292 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6292 (by decide) v hb
mask_input "6292|2553261366055435864928944128|151152620939976066203648"
end Percolation.MaskChain
