import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2182 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,false),(56,false)]
theorem inputList2182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2182 (by decide) v hb
mask_input "2182|90635492256645120|79228162514264355202909863936"
def inputClause2184 : CNF.NClause := [(96,true),(34,true),(39,true),(44,true),(49,false),(54,false),(56,false)]
theorem inputList2184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2184 (by decide) v hb
mask_input "2184|90634942500831232|79228162514264355752665677824"
def inputClause2185 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,false),(56,false)]
theorem inputList2185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2185 (by decide) v hb
mask_input "2185|90090151669137408|79228162514264900543497371648"
def inputClause2186 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,false),(56,false)]
theorem inputList2186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2186 (by decide) v hb
mask_input "2186|90090134489268224|79228162514264900560677240832"
def inputClause2188 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,true),(54,false),(56,false)]
theorem inputList2188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2188 (by decide) v hb
mask_input "2188|90089584733454336|79228162514264901110433054720"
def inputClause2190 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,false),(56,false)]
theorem inputList2190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2190 (by decide) v hb
mask_input "2190|90072542303223808|79228162514264918152863285248"
def inputClause2193 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,false),(54,true),(56,false)]
theorem inputList2193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2193 (by decide) v hb
mask_input "2193|72638703113076736|79228162514282351992053432320"
def inputClause2194 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,true),(56,false)]
theorem inputList2194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2194 (by decide) v hb
mask_input "2194|72638685933207552|79228162514282352009233301504"
def inputClause2197 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,true),(56,false)]
theorem inputList2197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2197 (by decide) v hb
mask_input "2197|72621110927032320|79228162514282369584239476736"
def inputClause2198 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,true),(56,false)]
theorem inputList2198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2198 (by decide) v hb
mask_input "2198|72621093747163136|79228162514282369601419345920"
def inputClause2201 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,true),(56,false)]
theorem inputList2201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2201 (by decide) v hb
mask_input "2201|72075753159655424|79228162514282914942006853632"
def inputClause2202 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,true),(56,false)]
theorem inputList2202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2202 (by decide) v hb
mask_input "2202|72075735979786240|79228162514282914959186722816"
def inputClause2203 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,true),(56,false)]
theorem inputList2203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2203 (by decide) v hb
mask_input "2203|72075203403841536|79228162514282915491762667520"
def inputClause2204 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,true),(54,true),(56,false)]
theorem inputList2204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2204 (by decide) v hb
mask_input "2204|72075186223972352|79228162514282915508942536704"
def inputClause2205 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,true),(56,false)]
theorem inputList2205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2205 (by decide) v hb
mask_input "2205|72058160973611008|79228162514282932534192898048"
def inputClause2206 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,true),(56,false)]
theorem inputList2206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2206 (by decide) v hb
mask_input "2206|72058143793741824|79228162514282932551372767232"
def inputClause2209 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,false),(54,false),(56,true)]
theorem inputList2209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2209 (by decide) v hb
mask_input "2209|18595507584630784|79228162514336395187581878272"
def inputClause2210 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,false),(56,true)]
theorem inputList2210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2210 (by decide) v hb
mask_input "2210|18595490404761600|79228162514336395204761747456"
def inputClause2211 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,false),(54,false),(56,true)]
theorem inputList2211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2211 (by decide) v hb
mask_input "2211|18594957828816896|79228162514336395737337692160"
def inputClause2212 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,false),(56,true)]
theorem inputList2212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2212 (by decide) v hb
mask_input "2212|18594940648947712|79228162514336395754517561344"
def inputClause2213 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,false),(56,true)]
theorem inputList2213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2213 (by decide) v hb
mask_input "2213|18577915398586368|79228162514336412779767922688"
def inputClause2214 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,false),(56,true)]
theorem inputList2214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2214 (by decide) v hb
mask_input "2214|18577898218717184|79228162514336412796947791872"
def inputClause2215 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,false),(54,false),(56,true)]
theorem inputList2215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2215 (by decide) v hb
mask_input "2215|18577365642772480|79228162514336413329523736576"
def inputClause2216 : CNF.NClause := [(96,true),(34,true),(39,true),(44,true),(49,false),(54,false),(56,true)]
theorem inputList2216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2216 (by decide) v hb
mask_input "2216|18577348462903296|79228162514336413346703605760"
def inputClause2217 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,false),(56,true)]
theorem inputList2217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2217 (by decide) v hb
mask_input "2217|18032557631209472|79228162514336958137535299584"
def inputClause2218 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,false),(56,true)]
theorem inputList2218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2218 (by decide) v hb
mask_input "2218|18032540451340288|79228162514336958154715168768"
def inputClause2219 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,false),(56,true)]
theorem inputList2219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2219 (by decide) v hb
mask_input "2219|18032007875395584|79228162514336958687291113472"
def inputClause2220 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,true),(54,false),(56,true)]
theorem inputList2220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2220 (by decide) v hb
mask_input "2220|18031990695526400|79228162514336958704470982656"
def inputClause2221 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(54,false),(56,true)]
theorem inputList2221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2221 (by decide) v hb
mask_input "2221|18014965445165056|79228162514336975729721344000"
def inputClause2222 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(54,false),(56,true)]
theorem inputList2222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2222 (by decide) v hb
mask_input "2222|18014948265295872|79228162514336975746901213184"
def inputClause2223 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,true),(54,false),(56,true)]
theorem inputList2223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2223 (by decide) v hb
mask_input "2223|18014415689351168|79228162514336976279477157888"
def inputClause2225 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,false),(54,true),(56,true)]
theorem inputList2225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2225 (by decide) v hb
mask_input "2225|581109075148800|79228162514354409586091360256"
def inputClause2226 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,true),(56,true)]
theorem inputList2226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2226 (by decide) v hb
mask_input "2226|581091895279616|79228162514354409603271229440"
def inputClause2227 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,false),(54,true),(56,true)]
theorem inputList2227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2227 (by decide) v hb
mask_input "2227|580559319334912|79228162514354410135847174144"
def inputClause2228 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,true),(56,true)]
theorem inputList2228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2228 (by decide) v hb
mask_input "2228|580542139465728|79228162514354410153027043328"
def inputClause2229 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,false),(54,true),(56,true)]
theorem inputList2229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2229 (by decide) v hb
mask_input "2229|563516889104384|79228162514354427178277404672"
def inputClause2230 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(54,true),(56,true)]
theorem inputList2230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2230 (by decide) v hb
mask_input "2230|563499709235200|79228162514354427195457273856"
def inputClause2231 : CNF.NClause := [(96,true),(34,false),(39,true),(44,true),(49,false),(54,true),(56,true)]
theorem inputList2231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2231 (by decide) v hb
mask_input "2231|562967133290496|79228162514354427728033218560"
def inputClause2233 : CNF.NClause := [(96,true),(34,false),(39,false),(44,false),(49,true),(54,true),(56,true)]
theorem inputList2233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2233 (by decide) v hb
mask_input "2233|18159121727488|79228162514354972536044781568"
def inputClause2234 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,true),(54,true),(56,true)]
theorem inputList2234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2234 (by decide) v hb
mask_input "2234|18141941858304|79228162514354972553224650752"
end Percolation.MaskChain
