import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause122 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,true),(25,true)]
theorem inputList122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause122 (by decide) v hb
mask_input "122|16896|9223372036905631760"
def inputClause123 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,true),(25,true)]
theorem inputList123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause123 (by decide) v hb
mask_input "123|16400|9223372036905632256"
def inputClause124 : CNF.NClause := [(63,false),(4,true),(9,true),(14,false),(19,true),(24,true),(25,true)]
theorem inputList124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause124 (by decide) v hb
mask_input "124|9223372036854792192|50856464"
def inputClause125 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,true),(24,true),(25,true)]
theorem inputList125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause125 (by decide) v hb
mask_input "125|528|9223372036905648128"
def inputClause126 : CNF.NClause := [(63,false),(4,true),(9,false),(14,true),(19,true),(24,true),(25,true)]
theorem inputList126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause126 (by decide) v hb
mask_input "126|9223372036854776320|50872336"
def inputClause127 : CNF.NClause := [(63,false),(4,false),(9,true),(14,true),(19,true),(24,true),(25,true)]
theorem inputList127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause127 (by decide) v hb
mask_input "127|9223372036854775824|50872832"
def inputClause128 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,true),(24,true),(25,true)]
theorem inputList128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause128 (by decide) v hb
mask_input "128|9223372036854775808|50872848"
def inputClause161 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,false),(22,false),(25,true)]
theorem inputList161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause161 (by decide) v hb
mask_input "161|4329604|18446744073743106048"
def inputClause162 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,false),(25,true)]
theorem inputList162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause162 (by decide) v hb
mask_input "162|4329600|18446744073743106052"
def inputClause163 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,false),(25,true)]
theorem inputList163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause163 (by decide) v hb
mask_input "163|4329476|18446744073743106176"
def inputClause164 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,false),(25,true)]
theorem inputList164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause164 (by decide) v hb
mask_input "164|4329472|18446744073743106180"
def inputClause165 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,false),(22,false),(25,true)]
theorem inputList165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause165 (by decide) v hb
mask_input "165|4325508|18446744073743110144"
def inputClause166 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,false),(25,true)]
theorem inputList166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause166 (by decide) v hb
mask_input "166|4325504|18446744073743110148"
def inputClause167 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,false),(25,true)]
theorem inputList167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause167 (by decide) v hb
mask_input "167|4325380|18446744073743110272"
def inputClause168 : CNF.NClause := [(64,true),(2,true),(7,true),(12,true),(17,false),(22,false),(25,true)]
theorem inputList168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause168 (by decide) v hb
mask_input "168|4325376|18446744073743110276"
def inputClause169 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,false),(25,true)]
theorem inputList169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause169 (by decide) v hb
mask_input "169|4198532|18446744073743237120"
def inputClause170 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,false),(25,true)]
theorem inputList170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause170 (by decide) v hb
mask_input "170|4198528|18446744073743237124"
def inputClause171 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,false),(25,true)]
theorem inputList171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause171 (by decide) v hb
mask_input "171|4198404|18446744073743237248"
def inputClause172 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,true),(22,false),(25,true)]
theorem inputList172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause172 (by decide) v hb
mask_input "172|4198400|18446744073743237252"
def inputClause173 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,true),(22,false),(25,true)]
theorem inputList173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause173 (by decide) v hb
mask_input "173|4194436|18446744073743241216"
def inputClause174 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,true),(22,false),(25,true)]
theorem inputList174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause174 (by decide) v hb
mask_input "174|4194432|18446744073743241220"
def inputClause175 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,true),(22,false),(25,true)]
theorem inputList175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause175 (by decide) v hb
mask_input "175|4194308|18446744073743241344"
def inputClause176 : CNF.NClause := [(64,false),(2,true),(7,true),(12,true),(17,true),(22,false),(25,true)]
theorem inputList176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause176 (by decide) v hb
mask_input "176|18446744073713745920|33689732"
def inputClause177 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,false),(22,true),(25,true)]
theorem inputList177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause177 (by decide) v hb
mask_input "177|135300|18446744073747300352"
def inputClause178 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,true),(25,true)]
theorem inputList178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause178 (by decide) v hb
mask_input "178|135296|18446744073747300356"
def inputClause179 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,true),(25,true)]
theorem inputList179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause179 (by decide) v hb
mask_input "179|135172|18446744073747300480"
def inputClause180 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,true),(25,true)]
theorem inputList180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause180 (by decide) v hb
mask_input "180|135168|18446744073747300484"
def inputClause181 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,false),(22,true),(25,true)]
theorem inputList181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause181 (by decide) v hb
mask_input "181|131204|18446744073747304448"
def inputClause182 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,true),(25,true)]
theorem inputList182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause182 (by decide) v hb
mask_input "182|131200|18446744073747304452"
def inputClause183 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,true),(25,true)]
theorem inputList183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause183 (by decide) v hb
mask_input "183|131076|18446744073747304576"
def inputClause184 : CNF.NClause := [(64,false),(2,true),(7,true),(12,true),(17,false),(22,true),(25,true)]
theorem inputList184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause184 (by decide) v hb
mask_input "184|18446744073709682688|37752964"
def inputClause185 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,true),(25,true)]
theorem inputList185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause185 (by decide) v hb
mask_input "185|4228|18446744073747431424"
def inputClause186 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,true),(25,true)]
theorem inputList186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause186 (by decide) v hb
mask_input "186|4224|18446744073747431428"
def inputClause187 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,true),(22,true),(25,true)]
theorem inputList187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause187 (by decide) v hb
mask_input "187|4100|18446744073747431552"
def inputClause188 : CNF.NClause := [(64,false),(2,true),(7,true),(12,false),(17,true),(22,true),(25,true)]
theorem inputList188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause188 (by decide) v hb
mask_input "188|18446744073709555712|37879940"
def inputClause189 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,true),(22,true),(25,true)]
theorem inputList189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause189 (by decide) v hb
mask_input "189|132|18446744073747435520"
def inputClause190 : CNF.NClause := [(64,false),(2,true),(7,false),(12,true),(17,true),(22,true),(25,true)]
theorem inputList190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause190 (by decide) v hb
mask_input "190|18446744073709551744|37883908"
def inputClause191 : CNF.NClause := [(64,false),(2,false),(7,true),(12,true),(17,true),(22,true),(25,true)]
theorem inputList191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause191 (by decide) v hb
mask_input "191|18446744073709551620|37884032"
def inputClause192 : CNF.NClause := [(64,false),(2,true),(7,true),(12,true),(17,true),(22,true),(25,true)]
theorem inputList192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) inputClause192 (by decide) v hb
mask_input "192|18446744073709551616|37884036"
def inputClause225 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,false),(23,false),(25,true)]
theorem inputList225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause225 (by decide) v hb
mask_input "225|8659208|36893488147452657664"
end Percolation.MaskChain
