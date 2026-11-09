import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3510 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,true),(58,true)]
theorem inputList3510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3510 (by decide) v hb
mask_input "3510|1125968626319360|83076749736557242349230730319495168"
def inputClause3511 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,true),(58,true)]
theorem inputList3511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3511 (by decide) v hb
mask_input "3511|1125917086711808|83076749736557242349230781859102720"
def inputClause3513 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,true),(58,true)]
theorem inputList3513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3513 (by decide) v hb
mask_input "3513|8881992368128|83076749736557242350347816953446400"
def inputClause3514 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,true),(58,true)]
theorem inputList3514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3514 (by decide) v hb
mask_input "3514|8864812498944|83076749736557242350347834133315584"
def inputClause3515 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,true),(58,true)]
theorem inputList3515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3515 (by decide) v hb
mask_input "3515|8813272891392|83076749736557242350347885672923136"
def inputClause3517 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(52,true),(58,true)]
theorem inputList3517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3517 (by decide) v hb
mask_input "3517|85899345920|83076749736557242350356613046468608"
def inputClause3520 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,true),(58,true)]
theorem inputList3520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3520 (by decide) v hb
mask_input "3520|83076749736557242056487941267521536|293868757678292992"
def inputClause3521 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,false),(60,false)]
theorem inputList3521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3521 (by decide) v hb
mask_input "3521|1162526911201542144|166153499473114484112975882535043072"
def inputClause3522 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,false),(60,false)]
theorem inputList3522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3522 (by decide) v hb
mask_input "3522|1162526906906574848|166153499473114484112975886830010368"
def inputClause3523 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,false),(60,false)]
theorem inputList3523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3523 (by decide) v hb
mask_input "3523|1162526842482065408|166153499473114484112975951254519808"
def inputClause3524 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,false),(60,false)]
theorem inputList3524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3524 (by decide) v hb
mask_input "3524|1162526838187098112|166153499473114484112975955549487104"
def inputClause3525 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,false),(60,false)]
theorem inputList3525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3525 (by decide) v hb
mask_input "3525|1162491726829453312|166153499473114484113011066907131904"
def inputClause3526 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,false),(60,false)]
theorem inputList3526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3526 (by decide) v hb
mask_input "3526|1162491722534486016|166153499473114484113011071202099200"
def inputClause3527 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,false),(60,false)]
theorem inputList3527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3527 (by decide) v hb
mask_input "3527|1162491658109976576|166153499473114484113011135626608640"
def inputClause3528 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,false),(60,false)]
theorem inputList3528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3528 (by decide) v hb
mask_input "3528|1162491653815009280|166153499473114484113011139921575936"
def inputClause3529 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,false),(60,false)]
theorem inputList3529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3529 (by decide) v hb
mask_input "3529|1161963961248120832|166153499473114484113538832488464384"
def inputClause3530 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,false),(60,false)]
theorem inputList3530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3530 (by decide) v hb
mask_input "3530|1161963956953153536|166153499473114484113538836783431680"
def inputClause3531 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,false),(60,false)]
theorem inputList3531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3531 (by decide) v hb
mask_input "3531|1161963892528644096|166153499473114484113538901207941120"
def inputClause3532 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,false),(60,false)]
theorem inputList3532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3532 (by decide) v hb
mask_input "3532|1161963888233676800|166153499473114484113538905502908416"
def inputClause3533 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,false),(60,false)]
theorem inputList3533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3533 (by decide) v hb
mask_input "3533|1161928776876032000|166153499473114484113574016860553216"
def inputClause3534 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,true),(53,false),(60,false)]
theorem inputList3534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3534 (by decide) v hb
mask_input "3534|1161928772581064704|166153499473114484113574021155520512"
def inputClause3535 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(53,false),(60,false)]
theorem inputList3535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3535 (by decide) v hb
mask_input "3535|1161928708156555264|166153499473114484113574085580029952"
def inputClause3536 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,true),(53,false),(60,false)]
theorem inputList3536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3536 (by decide) v hb
mask_input "3536|1161928703861587968|166153499473114484113574089874997248"
def inputClause3537 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,true),(60,false)]
theorem inputList3537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3537 (by decide) v hb
mask_input "3537|1153519711946801152|166153499473114484121983081789784064"
def inputClause3538 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,true),(60,false)]
theorem inputList3538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3538 (by decide) v hb
mask_input "3538|1153519707651833856|166153499473114484121983086084751360"
def inputClause3539 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,true),(60,false)]
theorem inputList3539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3539 (by decide) v hb
mask_input "3539|1153519643227324416|166153499473114484121983150509260800"
def inputClause3540 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,true),(60,false)]
theorem inputList3540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3540 (by decide) v hb
mask_input "3540|1153519638932357120|166153499473114484121983154804228096"
def inputClause3541 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,true),(60,false)]
theorem inputList3541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3541 (by decide) v hb
mask_input "3541|1153484527574712320|166153499473114484122018266161872896"
def inputClause3542 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,true),(60,false)]
theorem inputList3542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3542 (by decide) v hb
mask_input "3542|1153484523279745024|166153499473114484122018270456840192"
def inputClause3543 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,true),(60,false)]
theorem inputList3543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3543 (by decide) v hb
mask_input "3543|1153484458855235584|166153499473114484122018334881349632"
def inputClause3544 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,true),(60,false)]
theorem inputList3544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3544 (by decide) v hb
mask_input "3544|1153484454560268288|166153499473114484122018339176316928"
def inputClause3545 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,true),(60,false)]
theorem inputList3545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3545 (by decide) v hb
mask_input "3545|1152956761993379840|166153499473114484122546031743205376"
def inputClause3546 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,true),(60,false)]
theorem inputList3546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3546 (by decide) v hb
mask_input "3546|1152956757698412544|166153499473114484122546036038172672"
def inputClause3547 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,true),(60,false)]
theorem inputList3547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3547 (by decide) v hb
mask_input "3547|1152956693273903104|166153499473114484122546100462682112"
def inputClause3548 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,true),(60,false)]
theorem inputList3548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3548 (by decide) v hb
mask_input "3548|1152956688978935808|166153499473114484122546104757649408"
def inputClause3549 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,true),(60,false)]
theorem inputList3549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3549 (by decide) v hb
mask_input "3549|1152921577621291008|166153499473114484122581216115294208"
def inputClause3550 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,true),(53,true),(60,false)]
theorem inputList3550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3550 (by decide) v hb
mask_input "3550|1152921573326323712|166153499473114484122581220410261504"
def inputClause3551 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(53,true),(60,false)]
theorem inputList3551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3551 (by decide) v hb
mask_input "3551|1152921508901814272|166153499473114484122581284834770944"
def inputClause3553 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,false),(60,true)]
theorem inputList3553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3553 (by decide) v hb
mask_input "3553|9605406594695168|166153499473114485265897387141890048"
def inputClause3554 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,false),(60,true)]
theorem inputList3554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3554 (by decide) v hb
mask_input "3554|9605402299727872|166153499473114485265897391436857344"
end Percolation.MaskChain
