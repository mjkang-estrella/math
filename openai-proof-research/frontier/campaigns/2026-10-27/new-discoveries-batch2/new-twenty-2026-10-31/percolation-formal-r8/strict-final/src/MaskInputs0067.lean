import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3469 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,false),(58,false)]
theorem inputList3469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3469 (by decide) v hb
mask_input "3469|292734061678428160|83076749736557242057622637267386368"
def inputClause3470 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,true),(52,false),(58,false)]
theorem inputList3470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3470 (by decide) v hb
mask_input "3470|292734044498558976|83076749736557242057622654447255552"
def inputClause3471 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,false),(58,false)]
theorem inputList3471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3471 (by decide) v hb
mask_input "3471|292733992958951424|83076749736557242057622705986863104"
def inputClause3472 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,true),(52,false),(58,false)]
theorem inputList3472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3472 (by decide) v hb
mask_input "3472|292733975779082240|83076749736557242057622723166732288"
def inputClause3473 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,true),(58,false)]
theorem inputList3473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3473 (by decide) v hb
mask_input "3473|289365158050922496|83076749736557242060991540894892032"
def inputClause3474 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,true),(58,false)]
theorem inputList3474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3474 (by decide) v hb
mask_input "3474|289365140871053312|83076749736557242060991558074761216"
def inputClause3475 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,true),(58,false)]
theorem inputList3475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3475 (by decide) v hb
mask_input "3475|289365089331445760|83076749736557242060991609614368768"
def inputClause3476 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,true),(58,false)]
theorem inputList3476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3476 (by decide) v hb
mask_input "3476|289365072151576576|83076749736557242060991626794237952"
def inputClause3477 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,true),(58,false)]
theorem inputList3477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3477 (by decide) v hb
mask_input "3477|289356361957900288|83076749736557242061000336987914240"
def inputClause3478 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,true),(58,false)]
theorem inputList3478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3478 (by decide) v hb
mask_input "3478|289356344778031104|83076749736557242061000354167783424"
def inputClause3479 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,true),(58,false)]
theorem inputList3479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3479 (by decide) v hb
mask_input "3479|289356293238423552|83076749736557242061000405707390976"
def inputClause3480 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,false),(52,true),(58,false)]
theorem inputList3480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3480 (by decide) v hb
mask_input "3480|289356276058554368|83076749736557242061000422887260160"
def inputClause3481 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,true),(58,false)]
theorem inputList3481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3481 (by decide) v hb
mask_input "3481|288239258144079872|83076749736557242062117440801734656"
def inputClause3482 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,true),(58,false)]
theorem inputList3482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3482 (by decide) v hb
mask_input "3482|288239240964210688|83076749736557242062117457981603840"
def inputClause3483 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,true),(58,false)]
theorem inputList3483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3483 (by decide) v hb
mask_input "3483|288239189424603136|83076749736557242062117509521211392"
def inputClause3484 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,true),(52,true),(58,false)]
theorem inputList3484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3484 (by decide) v hb
mask_input "3484|288239172244733952|83076749736557242062117526701080576"
def inputClause3485 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,true),(58,false)]
theorem inputList3485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3485 (by decide) v hb
mask_input "3485|288230462051057664|83076749736557242062126236894756864"
def inputClause3486 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,true),(52,true),(58,false)]
theorem inputList3486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3486 (by decide) v hb
mask_input "3486|288230444871188480|83076749736557242062126254074626048"
def inputClause3487 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,true),(58,false)]
theorem inputList3487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3487 (by decide) v hb
mask_input "3487|288230393331580928|83076749736557242062126305614233600"
def inputClause3488 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,true),(58,false)]
theorem inputList3488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3488 (by decide) v hb
mask_input "3488|83076749736557242344718317419233280|5638381526581248"
def inputClause3489 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,false),(58,true)]
theorem inputList3489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3489 (by decide) v hb
mask_input "3489|5638381526581248|83076749736557242344718317419233280"
def inputClause3490 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,false),(58,true)]
theorem inputList3490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3490 (by decide) v hb
mask_input "3490|5638364346712064|83076749736557242344718334599102464"
def inputClause3491 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,false),(58,true)]
theorem inputList3491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3491 (by decide) v hb
mask_input "3491|5638312807104512|83076749736557242344718386138710016"
def inputClause3492 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,false),(58,true)]
theorem inputList3492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3492 (by decide) v hb
mask_input "3492|5638295627235328|83076749736557242344718403318579200"
def inputClause3493 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,false),(58,true)]
theorem inputList3493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3493 (by decide) v hb
mask_input "3493|5629585433559040|83076749736557242344727113512255488"
def inputClause3494 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,false),(58,true)]
theorem inputList3494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3494 (by decide) v hb
mask_input "3494|5629568253689856|83076749736557242344727130692124672"
def inputClause3495 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,false),(58,true)]
theorem inputList3495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3495 (by decide) v hb
mask_input "3495|5629516714082304|83076749736557242344727182231732224"
def inputClause3496 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,false),(52,false),(58,true)]
theorem inputList3496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3496 (by decide) v hb
mask_input "3496|5629499534213120|83076749736557242344727199411601408"
def inputClause3497 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,false),(58,true)]
theorem inputList3497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3497 (by decide) v hb
mask_input "3497|4512481619738624|83076749736557242345844217326075904"
def inputClause3498 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,false),(58,true)]
theorem inputList3498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3498 (by decide) v hb
mask_input "3498|4512464439869440|83076749736557242345844234505945088"
def inputClause3499 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,false),(58,true)]
theorem inputList3499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3499 (by decide) v hb
mask_input "3499|4512412900261888|83076749736557242345844286045552640"
def inputClause3500 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,true),(52,false),(58,true)]
theorem inputList3500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3500 (by decide) v hb
mask_input "3500|4512395720392704|83076749736557242345844303225421824"
def inputClause3501 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,false),(58,true)]
theorem inputList3501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3501 (by decide) v hb
mask_input "3501|4503685526716416|83076749736557242345853013419098112"
def inputClause3502 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,true),(52,false),(58,true)]
theorem inputList3502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3502 (by decide) v hb
mask_input "3502|4503668346847232|83076749736557242345853030598967296"
def inputClause3503 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,false),(58,true)]
theorem inputList3503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3503 (by decide) v hb
mask_input "3503|4503616807239680|83076749736557242345853082138574848"
def inputClause3505 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,true),(58,true)]
theorem inputList3505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3505 (by decide) v hb
mask_input "3505|1134781899210752|83076749736557242349221917046603776"
def inputClause3506 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,true),(58,true)]
theorem inputList3506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3506 (by decide) v hb
mask_input "3506|1134764719341568|83076749736557242349221934226472960"
def inputClause3507 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,true),(58,true)]
theorem inputList3507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3507 (by decide) v hb
mask_input "3507|1134713179734016|83076749736557242349221985766080512"
def inputClause3508 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,true),(58,true)]
theorem inputList3508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3508 (by decide) v hb
mask_input "3508|1134695999864832|83076749736557242349222002945949696"
def inputClause3509 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,true),(58,true)]
theorem inputList3509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3509 (by decide) v hb
mask_input "3509|1125985806188544|83076749736557242349230713139625984"
end Percolation.MaskChain
