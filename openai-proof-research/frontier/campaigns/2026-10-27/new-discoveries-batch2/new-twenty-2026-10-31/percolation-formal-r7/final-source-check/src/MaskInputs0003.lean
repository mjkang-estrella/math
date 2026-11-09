import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause298 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,false),(25,true)]
theorem inputList298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause298 (by decide) v hb
mask_input "298|2099264|73786976294871826434"
def inputClause299 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,false),(25,true)]
theorem inputList299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause299 (by decide) v hb
mask_input "299|2099202|73786976294871826496"
def inputClause300 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,true),(21,false),(25,true)]
theorem inputList300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause300 (by decide) v hb
mask_input "300|2099200|73786976294871826498"
def inputClause301 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,false),(25,true)]
theorem inputList301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause301 (by decide) v hb
mask_input "301|2097218|73786976294871828480"
def inputClause302 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,true),(21,false),(25,true)]
theorem inputList302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause302 (by decide) v hb
mask_input "302|2097216|73786976294871828482"
def inputClause303 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,true),(21,false),(25,true)]
theorem inputList303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause303 (by decide) v hb
mask_input "303|2097154|73786976294871828544"
def inputClause304 : CNF.NClause := [(66,false),(1,true),(6,true),(11,true),(16,true),(21,false),(25,true)]
theorem inputList304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause304 (by decide) v hb
mask_input "304|73786976294840303616|33622082"
def inputClause305 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,false),(21,true),(25,true)]
theorem inputList305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause305 (by decide) v hb
mask_input "305|67650|73786976294873858048"
def inputClause306 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,true),(25,true)]
theorem inputList306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause306 (by decide) v hb
mask_input "306|67648|73786976294873858050"
def inputClause307 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,true),(25,true)]
theorem inputList307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause307 (by decide) v hb
mask_input "307|67586|73786976294873858112"
def inputClause308 : CNF.NClause := [(66,true),(1,true),(6,true),(11,false),(16,false),(21,true),(25,true)]
theorem inputList308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause308 (by decide) v hb
mask_input "308|67584|73786976294873858114"
def inputClause309 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,true),(25,true)]
theorem inputList309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause309 (by decide) v hb
mask_input "309|65602|73786976294873860096"
def inputClause310 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,false),(21,true),(25,true)]
theorem inputList310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause310 (by decide) v hb
mask_input "310|65600|73786976294873860098"
def inputClause311 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(16,false),(21,true),(25,true)]
theorem inputList311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause311 (by decide) v hb
mask_input "311|65538|73786976294873860160"
def inputClause312 : CNF.NClause := [(66,false),(1,true),(6,true),(11,true),(16,false),(21,true),(25,true)]
theorem inputList312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause312 (by decide) v hb
mask_input "312|73786976294838272000|35653698"
def inputClause313 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,true),(21,true),(25,true)]
theorem inputList313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause313 (by decide) v hb
mask_input "313|2114|73786976294873923584"
def inputClause314 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,true),(25,true)]
theorem inputList314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause314 (by decide) v hb
mask_input "314|2112|73786976294873923586"
def inputClause315 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,true),(25,true)]
theorem inputList315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause315 (by decide) v hb
mask_input "315|2050|73786976294873923648"
def inputClause316 : CNF.NClause := [(66,false),(1,true),(6,true),(11,false),(16,true),(21,true),(25,true)]
theorem inputList316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause316 (by decide) v hb
mask_input "316|73786976294838208512|35717186"
def inputClause317 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,true),(25,true)]
theorem inputList317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause317 (by decide) v hb
mask_input "317|66|73786976294873925632"
def inputClause318 : CNF.NClause := [(66,false),(1,true),(6,false),(11,true),(16,true),(21,true),(25,true)]
theorem inputList318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause318 (by decide) v hb
mask_input "318|73786976294838206528|35719170"
def inputClause319 : CNF.NClause := [(66,false),(1,false),(6,true),(11,true),(16,true),(21,true),(25,true)]
theorem inputList319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause319 (by decide) v hb
mask_input "319|73786976294838206466|35719232"
def inputClause320 : CNF.NClause := [(66,false),(1,true),(6,true),(11,true),(16,true),(21,true),(25,true)]
theorem inputList320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) inputClause320 (by decide) v hb
mask_input "320|73786976294838206464|35719234"
def inputClause353 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,false),(24,false),(30,true)]
theorem inputList353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause353 (by decide) v hb
mask_input "353|32505856|147573952590750154752"
def inputClause354 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,false),(24,false),(30,true)]
theorem inputList354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause354 (by decide) v hb
mask_input "354|31457280|147573952590751203328"
def inputClause355 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,false),(24,false),(30,true)]
theorem inputList355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause355 (by decide) v hb
mask_input "355|30408704|147573952590752251904"
def inputClause356 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,false),(30,true)]
theorem inputList356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause356 (by decide) v hb
mask_input "356|29360128|147573952590753300480"
def inputClause357 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,false),(24,false),(30,true)]
theorem inputList357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause357 (by decide) v hb
mask_input "357|28311552|147573952590754349056"
def inputClause358 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,false),(24,false),(30,true)]
theorem inputList358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause358 (by decide) v hb
mask_input "358|27262976|147573952590755397632"
def inputClause359 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,false),(24,false),(30,true)]
theorem inputList359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause359 (by decide) v hb
mask_input "359|26214400|147573952590756446208"
def inputClause360 : CNF.NClause := [(67,true),(20,true),(21,true),(22,true),(23,false),(24,false),(30,true)]
theorem inputList360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause360 (by decide) v hb
mask_input "360|25165824|147573952590757494784"
def inputClause361 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,true),(24,false),(30,true)]
theorem inputList361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause361 (by decide) v hb
mask_input "361|24117248|147573952590758543360"
def inputClause362 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,true),(24,false),(30,true)]
theorem inputList362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause362 (by decide) v hb
mask_input "362|23068672|147573952590759591936"
def inputClause363 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,true),(24,false),(30,true)]
theorem inputList363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause363 (by decide) v hb
mask_input "363|22020096|147573952590760640512"
def inputClause364 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,true),(24,false),(30,true)]
theorem inputList364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause364 (by decide) v hb
mask_input "364|20971520|147573952590761689088"
def inputClause365 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,true),(24,false),(30,true)]
theorem inputList365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause365 (by decide) v hb
mask_input "365|19922944|147573952590762737664"
def inputClause366 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,true),(24,false),(30,true)]
theorem inputList366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause366 (by decide) v hb
mask_input "366|18874368|147573952590763786240"
def inputClause367 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,true),(24,false),(30,true)]
theorem inputList367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause367 (by decide) v hb
mask_input "367|17825792|147573952590764834816"
def inputClause368 : CNF.NClause := [(67,false),(20,true),(21,true),(22,true),(23,true),(24,false),(30,true)]
theorem inputList368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause368 (by decide) v hb
mask_input "368|147573952589693190144|1089470464"
def inputClause369 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,false),(24,true),(30,true)]
theorem inputList369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause369 (by decide) v hb
mask_input "369|15728640|147573952590766931968"
end Percolation.MaskChain
