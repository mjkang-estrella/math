import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3424 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,true),(59,false)]
theorem inputList3424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3424 (by decide) v hb
mask_input "3424|41538374868278621604704722937184256|36187204002775040"
def inputClause3425 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,false),(59,true)]
theorem inputList3425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3425 (by decide) v hb
mask_input "3425|36187204002775040|41538374868278621604704722937184256"
def inputClause3426 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,false),(59,true)]
theorem inputList3426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3426 (by decide) v hb
mask_input "3426|36187195412840448|41538374868278621604704731527118848"
def inputClause3427 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,false),(59,true)]
theorem inputList3427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3427 (by decide) v hb
mask_input "3427|36187135283298304|41538374868278621604704791656660992"
def inputClause3428 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,false),(59,true)]
theorem inputList3428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3428 (by decide) v hb
mask_input "3428|36187126693363712|41538374868278621604704800246595584"
def inputClause3429 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,false),(59,true)]
theorem inputList3429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3429 (by decide) v hb
mask_input "3429|36169611816730624|41538374868278621604722315123228672"
def inputClause3430 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,false),(59,true)]
theorem inputList3430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3430 (by decide) v hb
mask_input "3430|36169603226796032|41538374868278621604722323713163264"
def inputClause3431 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,false),(59,true)]
theorem inputList3431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3431 (by decide) v hb
mask_input "3431|36169543097253888|41538374868278621604722383842705408"
def inputClause3432 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,false),(55,false),(59,true)]
theorem inputList3432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3432 (by decide) v hb
mask_input "3432|36169534507319296|41538374868278621604722392432640000"
def inputClause3433 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,false),(59,true)]
theorem inputList3433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3433 (by decide) v hb
mask_input "3433|36046466514419712|41538374868278621604845460425539584"
def inputClause3434 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,false),(59,true)]
theorem inputList3434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3434 (by decide) v hb
mask_input "3434|36046457924485120|41538374868278621604845469015474176"
def inputClause3435 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,false),(59,true)]
theorem inputList3435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3435 (by decide) v hb
mask_input "3435|36046397794942976|41538374868278621604845529145016320"
def inputClause3436 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,true),(55,false),(59,true)]
theorem inputList3436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3436 (by decide) v hb
mask_input "3436|36046389205008384|41538374868278621604845537734950912"
def inputClause3437 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,false),(59,true)]
theorem inputList3437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3437 (by decide) v hb
mask_input "3437|36028874328375296|41538374868278621604863052611584000"
def inputClause3438 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,true),(55,false),(59,true)]
theorem inputList3438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3438 (by decide) v hb
mask_input "3438|36028865738440704|41538374868278621604863061201518592"
def inputClause3439 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,false),(59,true)]
theorem inputList3439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3439 (by decide) v hb
mask_input "3439|36028805608898560|41538374868278621604863121331060736"
def inputClause3441 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,true),(59,true)]
theorem inputList3441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3441 (by decide) v hb
mask_input "3441|158406983811072|41538374868278621640733519956148224"
def inputClause3442 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,true),(59,true)]
theorem inputList3442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3442 (by decide) v hb
mask_input "3442|158398393876480|41538374868278621640733528546082816"
def inputClause3443 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,true),(59,true)]
theorem inputList3443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3443 (by decide) v hb
mask_input "3443|158338264334336|41538374868278621640733588675624960"
def inputClause3444 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,true),(59,true)]
theorem inputList3444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3444 (by decide) v hb
mask_input "3444|158329674399744|41538374868278621640733597265559552"
def inputClause3445 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,true),(59,true)]
theorem inputList3445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3445 (by decide) v hb
mask_input "3445|140814797766656|41538374868278621640751112142192640"
def inputClause3446 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,true),(59,true)]
theorem inputList3446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3446 (by decide) v hb
mask_input "3446|140806207832064|41538374868278621640751120732127232"
def inputClause3447 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,true),(59,true)]
theorem inputList3447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3447 (by decide) v hb
mask_input "3447|140746078289920|41538374868278621640751180861669376"
def inputClause3449 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,true),(59,true)]
theorem inputList3449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3449 (by decide) v hb
mask_input "3449|17669495455744|41538374868278621640874257444503552"
def inputClause3450 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,true),(59,true)]
theorem inputList3450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3450 (by decide) v hb
mask_input "3450|17660905521152|41538374868278621640874266034438144"
def inputClause3451 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,true),(59,true)]
theorem inputList3451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3451 (by decide) v hb
mask_input "3451|17600775979008|41538374868278621640874326163980288"
def inputClause3453 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,true),(59,true)]
theorem inputList3453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3453 (by decide) v hb
mask_input "3453|77309411328|41538374868278621640891849630547968"
def inputClause3456 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,true),(59,true)]
theorem inputList3456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3456 (by decide) v hb
mask_input "3456|41538374868278621028243970633760768|612647956306198528"
def inputClause3457 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,false),(52,false),(58,false)]
theorem inputList3457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3457 (by decide) v hb
mask_input "3457|293868757678292992|83076749736557242056487941267521536"
def inputClause3458 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,false),(52,false),(58,false)]
theorem inputList3458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3458 (by decide) v hb
mask_input "3458|293868740498423808|83076749736557242056487958447390720"
def inputClause3459 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,false),(58,false)]
theorem inputList3459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3459 (by decide) v hb
mask_input "3459|293868688958816256|83076749736557242056488009986998272"
def inputClause3460 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,false),(52,false),(58,false)]
theorem inputList3460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3460 (by decide) v hb
mask_input "3460|293868671778947072|83076749736557242056488027166867456"
def inputClause3461 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,false),(52,false),(58,false)]
theorem inputList3461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3461 (by decide) v hb
mask_input "3461|293859961585270784|83076749736557242056496737360543744"
def inputClause3462 : CNF.NClause := [(116,true),(34,true),(36,false),(43,true),(50,false),(52,false),(58,false)]
theorem inputList3462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3462 (by decide) v hb
mask_input "3462|293859944405401600|83076749736557242056496754540412928"
def inputClause3463 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,false),(58,false)]
theorem inputList3463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3463 (by decide) v hb
mask_input "3463|293859892865794048|83076749736557242056496806080020480"
def inputClause3464 : CNF.NClause := [(116,true),(34,true),(36,true),(43,true),(50,false),(52,false),(58,false)]
theorem inputList3464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3464 (by decide) v hb
mask_input "3464|293859875685924864|83076749736557242056496823259889664"
def inputClause3465 : CNF.NClause := [(116,true),(34,false),(36,false),(43,false),(50,true),(52,false),(58,false)]
theorem inputList3465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3465 (by decide) v hb
mask_input "3465|292742857771450368|83076749736557242057613841174364160"
def inputClause3466 : CNF.NClause := [(116,true),(34,true),(36,false),(43,false),(50,true),(52,false),(58,false)]
theorem inputList3466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3466 (by decide) v hb
mask_input "3466|292742840591581184|83076749736557242057613858354233344"
def inputClause3467 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,false),(58,false)]
theorem inputList3467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3467 (by decide) v hb
mask_input "3467|292742789051973632|83076749736557242057613909893840896"
def inputClause3468 : CNF.NClause := [(116,true),(34,true),(36,true),(43,false),(50,true),(52,false),(58,false)]
theorem inputList3468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3468 (by decide) v hb
mask_input "3468|292742771872104448|83076749736557242057613927073710080"
end Percolation.MaskChain
