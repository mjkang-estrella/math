import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3380 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,true),(57,true)]
theorem inputList3380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3380 (by decide) v hb
mask_input "3380|285873023221760|20769187434139310676251674981433344"
def inputClause3381 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,true),(57,true)]
theorem inputList3381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3381 (by decide) v hb
mask_input "3381|281578055925760|20769187434139310676255969948729344"
def inputClause3382 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,true),(57,true)]
theorem inputList3382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3382 (by decide) v hb
mask_input "3382|281543696187392|20769187434139310676256004308467712"
def inputClause3383 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,true),(57,true)]
theorem inputList3383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3383 (by decide) v hb
mask_input "3383|281509336449024|20769187434139310676256038668206080"
def inputClause3385 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,true),(57,true)]
theorem inputList3385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3385 (by decide) v hb
mask_input "3385|4501125726208|20769187434139310676533046878928896"
def inputClause3386 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,true),(57,true)]
theorem inputList3386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3386 (by decide) v hb
mask_input "3386|4466765987840|20769187434139310676533081238667264"
def inputClause3387 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,true),(57,true)]
theorem inputList3387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3387 (by decide) v hb
mask_input "3387|4432406249472|20769187434139310676533115598405632"
def inputClause3389 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,true),(57,true)]
theorem inputList3389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3389 (by decide) v hb
mask_input "3389|103079215104|20769187434139310676537444925440000"
def inputClause3392 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,true),(57,true)]
theorem inputList3392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3392 (by decide) v hb
mask_input "3392|20769187434139310514121985316880384|162415562687774720"
def inputClause3393 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,false),(59,false)]
theorem inputList3393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3393 (by decide) v hb
mask_input "3393|612647956306198528|41538374868278621028243970633760768"
def inputClause3394 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,false),(59,false)]
theorem inputList3394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3394 (by decide) v hb
mask_input "3394|612647947716263936|41538374868278621028243979223695360"
def inputClause3395 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,false),(59,false)]
theorem inputList3395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3395 (by decide) v hb
mask_input "3395|612647887586721792|41538374868278621028244039353237504"
def inputClause3396 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,false),(59,false)]
theorem inputList3396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3396 (by decide) v hb
mask_input "3396|612647878996787200|41538374868278621028244047943172096"
def inputClause3397 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,false),(59,false)]
theorem inputList3397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3397 (by decide) v hb
mask_input "3397|612630364120154112|41538374868278621028261562819805184"
def inputClause3398 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,false),(59,false)]
theorem inputList3398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3398 (by decide) v hb
mask_input "3398|612630355530219520|41538374868278621028261571409739776"
def inputClause3399 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,false),(59,false)]
theorem inputList3399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3399 (by decide) v hb
mask_input "3399|612630295400677376|41538374868278621028261631539281920"
def inputClause3400 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,false),(55,false),(59,false)]
theorem inputList3400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3400 (by decide) v hb
mask_input "3400|612630286810742784|41538374868278621028261640129216512"
def inputClause3401 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,false),(59,false)]
theorem inputList3401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3401 (by decide) v hb
mask_input "3401|612507218817843200|41538374868278621028384708122116096"
def inputClause3402 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,false),(59,false)]
theorem inputList3402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3402 (by decide) v hb
mask_input "3402|612507210227908608|41538374868278621028384716712050688"
def inputClause3403 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,false),(59,false)]
theorem inputList3403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3403 (by decide) v hb
mask_input "3403|612507150098366464|41538374868278621028384776841592832"
def inputClause3404 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,true),(55,false),(59,false)]
theorem inputList3404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3404 (by decide) v hb
mask_input "3404|612507141508431872|41538374868278621028384785431527424"
def inputClause3405 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,false),(59,false)]
theorem inputList3405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3405 (by decide) v hb
mask_input "3405|612489626631798784|41538374868278621028402300308160512"
def inputClause3406 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,true),(55,false),(59,false)]
theorem inputList3406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3406 (by decide) v hb
mask_input "3406|612489618041864192|41538374868278621028402308898095104"
def inputClause3407 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,false),(59,false)]
theorem inputList3407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3407 (by decide) v hb
mask_input "3407|612489557912322048|41538374868278621028402369027637248"
def inputClause3408 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,true),(55,false),(59,false)]
theorem inputList3408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3408 (by decide) v hb
mask_input "3408|612489549322387456|41538374868278621028402377617571840"
def inputClause3409 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,false),(55,true),(59,false)]
theorem inputList3409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3409 (by decide) v hb
mask_input "3409|576619159287234560|41538374868278621064272767652724736"
def inputClause3410 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,false),(55,true),(59,false)]
theorem inputList3410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3410 (by decide) v hb
mask_input "3410|576619150697299968|41538374868278621064272776242659328"
def inputClause3411 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,false),(55,true),(59,false)]
theorem inputList3411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3411 (by decide) v hb
mask_input "3411|576619090567757824|41538374868278621064272836372201472"
def inputClause3412 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,false),(55,true),(59,false)]
theorem inputList3412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3412 (by decide) v hb
mask_input "3412|576619081977823232|41538374868278621064272844962136064"
def inputClause3413 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,false),(55,true),(59,false)]
theorem inputList3413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3413 (by decide) v hb
mask_input "3413|576601567101190144|41538374868278621064290359838769152"
def inputClause3414 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,false),(55,true),(59,false)]
theorem inputList3414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3414 (by decide) v hb
mask_input "3414|576601558511255552|41538374868278621064290368428703744"
def inputClause3415 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,false),(55,true),(59,false)]
theorem inputList3415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3415 (by decide) v hb
mask_input "3415|576601498381713408|41538374868278621064290428558245888"
def inputClause3416 : CNF.NClause := [(115,true),(33,true),(36,true),(44,true),(47,false),(55,true),(59,false)]
theorem inputList3416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3416 (by decide) v hb
mask_input "3416|576601489791778816|41538374868278621064290437148180480"
def inputClause3417 : CNF.NClause := [(115,true),(33,false),(36,false),(44,false),(47,true),(55,true),(59,false)]
theorem inputList3417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3417 (by decide) v hb
mask_input "3417|576478421798879232|41538374868278621064413505141080064"
def inputClause3418 : CNF.NClause := [(115,true),(33,true),(36,false),(44,false),(47,true),(55,true),(59,false)]
theorem inputList3418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3418 (by decide) v hb
mask_input "3418|576478413208944640|41538374868278621064413513731014656"
def inputClause3419 : CNF.NClause := [(115,true),(33,false),(36,true),(44,false),(47,true),(55,true),(59,false)]
theorem inputList3419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3419 (by decide) v hb
mask_input "3419|576478353079402496|41538374868278621064413573860556800"
def inputClause3420 : CNF.NClause := [(115,true),(33,true),(36,true),(44,false),(47,true),(55,true),(59,false)]
theorem inputList3420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3420 (by decide) v hb
mask_input "3420|576478344489467904|41538374868278621064413582450491392"
def inputClause3421 : CNF.NClause := [(115,true),(33,false),(36,false),(44,true),(47,true),(55,true),(59,false)]
theorem inputList3421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3421 (by decide) v hb
mask_input "3421|576460829612834816|41538374868278621064431097327124480"
def inputClause3422 : CNF.NClause := [(115,true),(33,true),(36,false),(44,true),(47,true),(55,true),(59,false)]
theorem inputList3422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3422 (by decide) v hb
mask_input "3422|576460821022900224|41538374868278621064431105917059072"
def inputClause3423 : CNF.NClause := [(115,true),(33,false),(36,true),(44,true),(47,true),(55,true),(59,false)]
theorem inputList3423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3423 (by decide) v hb
mask_input "3423|576460760893358080|41538374868278621064431166046601216"
end Percolation.MaskChain
