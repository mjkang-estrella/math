import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause226 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,false),(25,true)]
theorem inputList226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause226 (by decide) v hb
mask_input "226|8659200|36893488147452657672"
def inputClause227 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,false),(25,true)]
theorem inputList227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause227 (by decide) v hb
mask_input "227|8658952|36893488147452657920"
def inputClause228 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,false),(25,true)]
theorem inputList228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause228 (by decide) v hb
mask_input "228|8658944|36893488147452657928"
def inputClause229 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,false),(23,false),(25,true)]
theorem inputList229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause229 (by decide) v hb
mask_input "229|8651016|36893488147452665856"
def inputClause230 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,false),(25,true)]
theorem inputList230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause230 (by decide) v hb
mask_input "230|8651008|36893488147452665864"
def inputClause231 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,false),(25,true)]
theorem inputList231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause231 (by decide) v hb
mask_input "231|8650760|36893488147452666112"
def inputClause232 : CNF.NClause := [(65,true),(3,true),(8,true),(13,true),(18,false),(23,false),(25,true)]
theorem inputList232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause232 (by decide) v hb
mask_input "232|8650752|36893488147452666120"
def inputClause233 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,true),(23,false),(25,true)]
theorem inputList233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause233 (by decide) v hb
mask_input "233|8397064|36893488147452919808"
def inputClause234 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,true),(23,false),(25,true)]
theorem inputList234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause234 (by decide) v hb
mask_input "234|8397056|36893488147452919816"
def inputClause235 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,false),(25,true)]
theorem inputList235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause235 (by decide) v hb
mask_input "235|8396808|36893488147452920064"
def inputClause236 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,true),(23,false),(25,true)]
theorem inputList236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause236 (by decide) v hb
mask_input "236|8396800|36893488147452920072"
def inputClause237 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,false),(25,true)]
theorem inputList237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause237 (by decide) v hb
mask_input "237|8388872|36893488147452928000"
def inputClause238 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,true),(23,false),(25,true)]
theorem inputList238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause238 (by decide) v hb
mask_input "238|8388864|36893488147452928008"
def inputClause239 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,true),(23,false),(25,true)]
theorem inputList239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause239 (by decide) v hb
mask_input "239|8388616|36893488147452928256"
def inputClause240 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,true),(23,false),(25,true)]
theorem inputList240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause240 (by decide) v hb
mask_input "240|36893488147427491840|33825032"
def inputClause241 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,false),(23,true),(25,true)]
theorem inputList241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause241 (by decide) v hb
mask_input "241|270600|36893488147461046272"
def inputClause242 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,true),(25,true)]
theorem inputList242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause242 (by decide) v hb
mask_input "242|270592|36893488147461046280"
def inputClause243 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,true),(25,true)]
theorem inputList243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause243 (by decide) v hb
mask_input "243|270344|36893488147461046528"
def inputClause244 : CNF.NClause := [(65,true),(3,true),(8,true),(13,false),(18,false),(23,true),(25,true)]
theorem inputList244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause244 (by decide) v hb
mask_input "244|270336|36893488147461046536"
def inputClause245 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,false),(23,true),(25,true)]
theorem inputList245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause245 (by decide) v hb
mask_input "245|262408|36893488147461054464"
def inputClause246 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,true),(25,true)]
theorem inputList246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause246 (by decide) v hb
mask_input "246|262400|36893488147461054472"
def inputClause247 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,true),(25,true)]
theorem inputList247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause247 (by decide) v hb
mask_input "247|262152|36893488147461054720"
def inputClause248 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,false),(23,true),(25,true)]
theorem inputList248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause248 (by decide) v hb
mask_input "248|36893488147419365376|41951496"
def inputClause249 : CNF.NClause := [(65,true),(3,false),(8,false),(13,false),(18,true),(23,true),(25,true)]
theorem inputList249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause249 (by decide) v hb
mask_input "249|8456|36893488147461308416"
def inputClause250 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,true),(23,true),(25,true)]
theorem inputList250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause250 (by decide) v hb
mask_input "250|8448|36893488147461308424"
def inputClause251 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,true),(25,true)]
theorem inputList251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause251 (by decide) v hb
mask_input "251|8200|36893488147461308672"
def inputClause252 : CNF.NClause := [(65,false),(3,true),(8,true),(13,false),(18,true),(23,true),(25,true)]
theorem inputList252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause252 (by decide) v hb
mask_input "252|36893488147419111424|42205448"
def inputClause253 : CNF.NClause := [(65,true),(3,false),(8,false),(13,true),(18,true),(23,true),(25,true)]
theorem inputList253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause253 (by decide) v hb
mask_input "253|264|36893488147461316608"
def inputClause254 : CNF.NClause := [(65,false),(3,true),(8,false),(13,true),(18,true),(23,true),(25,true)]
theorem inputList254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause254 (by decide) v hb
mask_input "254|36893488147419103488|42213384"
def inputClause255 : CNF.NClause := [(65,false),(3,false),(8,true),(13,true),(18,true),(23,true),(25,true)]
theorem inputList255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause255 (by decide) v hb
mask_input "255|36893488147419103240|42213632"
def inputClause256 : CNF.NClause := [(65,false),(3,true),(8,true),(13,true),(18,true),(23,true),(25,true)]
theorem inputList256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 3) 3) (activationA_mem 3) inputClause256 (by decide) v hb
mask_input "256|36893488147419103232|42213640"
def inputClause289 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,false),(21,false),(25,true)]
theorem inputList289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause289 (by decide) v hb
mask_input "289|2164802|73786976294871760896"
def inputClause290 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,false),(25,true)]
theorem inputList290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause290 (by decide) v hb
mask_input "290|2164800|73786976294871760898"
def inputClause291 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,false),(25,true)]
theorem inputList291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause291 (by decide) v hb
mask_input "291|2164738|73786976294871760960"
def inputClause292 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,false),(21,false),(25,true)]
theorem inputList292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause292 (by decide) v hb
mask_input "292|2164736|73786976294871760962"
def inputClause293 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,false),(25,true)]
theorem inputList293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause293 (by decide) v hb
mask_input "293|2162754|73786976294871762944"
def inputClause294 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,false),(21,false),(25,true)]
theorem inputList294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause294 (by decide) v hb
mask_input "294|2162752|73786976294871762946"
def inputClause295 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,false),(21,false),(25,true)]
theorem inputList295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause295 (by decide) v hb
mask_input "295|2162690|73786976294871763008"
def inputClause296 : CNF.NClause := [(66,true),(1,true),(6,true),(11,true),(16,false),(21,false),(25,true)]
theorem inputList296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause296 (by decide) v hb
mask_input "296|2162688|73786976294871763010"
def inputClause297 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,true),(21,false),(25,true)]
theorem inputList297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause297 (by decide) v hb
mask_input "297|2099266|73786976294871826432"
end Percolation.MaskChain
