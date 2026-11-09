import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause498 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,true),(27,true)]
theorem inputList498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause498 (by decide) v hb
mask_input "498|264704|590295810358840918020"
def inputClause499 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,false),(20,true),(27,true)]
theorem inputList499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause499 (by decide) v hb
mask_input "499|264196|590295810358840918528"
def inputClause500 : CNF.NClause := [(69,true),(2,true),(9,true),(11,false),(18,false),(20,true),(27,true)]
theorem inputList500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause500 (by decide) v hb
mask_input "500|264192|590295810358840918532"
def inputClause501 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,false),(20,true),(27,true)]
theorem inputList501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause501 (by decide) v hb
mask_input "501|262660|590295810358840920064"
def inputClause502 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(18,false),(20,true),(27,true)]
theorem inputList502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause502 (by decide) v hb
mask_input "502|262656|590295810358840920068"
def inputClause503 : CNF.NClause := [(69,true),(2,false),(9,true),(11,true),(18,false),(20,true),(27,true)]
theorem inputList503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause503 (by decide) v hb
mask_input "503|262148|590295810358840920576"
def inputClause505 : CNF.NClause := [(69,true),(2,false),(9,false),(11,false),(18,true),(20,true),(27,true)]
theorem inputList505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause505 (by decide) v hb
mask_input "505|2564|590295810358841180160"
def inputClause506 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,true),(20,true),(27,true)]
theorem inputList506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause506 (by decide) v hb
mask_input "506|2560|590295810358841180164"
def inputClause507 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(18,true),(20,true),(27,true)]
theorem inputList507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause507 (by decide) v hb
mask_input "507|2052|590295810358841180672"
def inputClause509 : CNF.NClause := [(69,true),(2,false),(9,false),(11,true),(18,true),(20,true),(27,true)]
theorem inputList509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause509 (by decide) v hb
mask_input "509|516|590295810358841182208"
def inputClause510 : CNF.NClause := [(69,false),(2,true),(9,false),(11,true),(18,true),(20,true),(27,true)]
theorem inputList510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause510 (by decide) v hb
mask_input "510|590295810358705652224|135530500"
def inputClause512 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,true),(27,true)]
theorem inputList512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause512 (by decide) v hb
mask_input "512|590295810358705651712|135531012"
def inputClause513 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,false),(28,false)]
theorem inputList513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause513 (by decide) v hb
mask_input "513|269631560|1180591620717411303424"
def inputClause514 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,false),(28,false)]
theorem inputList514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause514 (by decide) v hb
mask_input "514|269631552|1180591620717411303432"
def inputClause515 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,false),(28,false)]
theorem inputList515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause515 (by decide) v hb
mask_input "515|269631496|1180591620717411303488"
def inputClause516 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,false),(28,false)]
theorem inputList516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause516 (by decide) v hb
mask_input "516|269631488|1180591620717411303496"
def inputClause517 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,false),(28,false)]
theorem inputList517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause517 (by decide) v hb
mask_input "517|269615176|1180591620717411319808"
def inputClause518 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,false),(28,false)]
theorem inputList518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause518 (by decide) v hb
mask_input "518|269615168|1180591620717411319816"
def inputClause519 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,false),(28,false)]
theorem inputList519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause519 (by decide) v hb
mask_input "519|269615112|1180591620717411319872"
def inputClause520 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,false),(20,false),(28,false)]
theorem inputList520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause520 (by decide) v hb
mask_input "520|269615104|1180591620717411319880"
def inputClause521 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,false),(28,false)]
theorem inputList521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause521 (by decide) v hb
mask_input "521|269500488|1180591620717411434496"
def inputClause522 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,false),(28,false)]
theorem inputList522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause522 (by decide) v hb
mask_input "522|269500480|1180591620717411434504"
def inputClause523 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,false),(28,false)]
theorem inputList523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause523 (by decide) v hb
mask_input "523|269500424|1180591620717411434560"
def inputClause524 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,true),(20,false),(28,false)]
theorem inputList524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause524 (by decide) v hb
mask_input "524|269500416|1180591620717411434568"
def inputClause525 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,false),(28,false)]
theorem inputList525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause525 (by decide) v hb
mask_input "525|269484104|1180591620717411450880"
def inputClause526 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,false),(28,false)]
theorem inputList526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause526 (by decide) v hb
mask_input "526|269484096|1180591620717411450888"
def inputClause527 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,true),(20,false),(28,false)]
theorem inputList527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause527 (by decide) v hb
mask_input "527|269484040|1180591620717411450944"
def inputClause528 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,true),(20,false),(28,false)]
theorem inputList528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause528 (by decide) v hb
mask_input "528|269484032|1180591620717411450952"
def inputClause529 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,true),(28,false)]
theorem inputList529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause529 (by decide) v hb
mask_input "529|268582984|1180591620717412352000"
def inputClause530 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,true),(28,false)]
theorem inputList530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause530 (by decide) v hb
mask_input "530|268582976|1180591620717412352008"
def inputClause531 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,true),(28,false)]
theorem inputList531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause531 (by decide) v hb
mask_input "531|268582920|1180591620717412352064"
def inputClause532 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,true),(28,false)]
theorem inputList532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause532 (by decide) v hb
mask_input "532|268582912|1180591620717412352072"
def inputClause533 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,true),(28,false)]
theorem inputList533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause533 (by decide) v hb
mask_input "533|268566600|1180591620717412368384"
def inputClause534 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,true),(28,false)]
theorem inputList534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause534 (by decide) v hb
mask_input "534|268566592|1180591620717412368392"
def inputClause535 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,true),(28,false)]
theorem inputList535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause535 (by decide) v hb
mask_input "535|268566536|1180591620717412368448"
def inputClause536 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,false),(20,true),(28,false)]
theorem inputList536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause536 (by decide) v hb
mask_input "536|268566528|1180591620717412368456"
def inputClause537 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,true),(28,false)]
theorem inputList537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause537 (by decide) v hb
mask_input "537|268451912|1180591620717412483072"
def inputClause538 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,true),(28,false)]
theorem inputList538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause538 (by decide) v hb
mask_input "538|268451904|1180591620717412483080"
def inputClause539 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,true),(28,false)]
theorem inputList539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause539 (by decide) v hb
mask_input "539|268451848|1180591620717412483136"
def inputClause540 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,true),(20,true),(28,false)]
theorem inputList540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause540 (by decide) v hb
mask_input "540|268451840|1180591620717412483144"
end Percolation.MaskChain
