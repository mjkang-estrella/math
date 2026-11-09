import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3555 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,false),(60,true)]
theorem inputList3555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3555 (by decide) v hb
mask_input "3555|9605337875218432|166153499473114485265897455861366784"
def inputClause3556 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,false),(60,true)]
theorem inputList3556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3556 (by decide) v hb
mask_input "3556|9605333580251136|166153499473114485265897460156334080"
def inputClause3557 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,false),(60,true)]
theorem inputList3557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3557 (by decide) v hb
mask_input "3557|9570222222606336|166153499473114485265932571513978880"
def inputClause3558 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,false),(60,true)]
theorem inputList3558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3558 (by decide) v hb
mask_input "3558|9570217927639040|166153499473114485265932575808946176"
def inputClause3559 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,false),(60,true)]
theorem inputList3559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3559 (by decide) v hb
mask_input "3559|9570153503129600|166153499473114485265932640233455616"
def inputClause3560 : CNF.NClause := [(117,true),(32,true),(36,true),(45,true),(49,false),(53,false),(60,true)]
theorem inputList3560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3560 (by decide) v hb
mask_input "3560|9570149208162304|166153499473114485265932644528422912"
def inputClause3561 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,false),(60,true)]
theorem inputList3561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3561 (by decide) v hb
mask_input "3561|9042456641273856|166153499473114485266460337095311360"
def inputClause3562 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,false),(60,true)]
theorem inputList3562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3562 (by decide) v hb
mask_input "3562|9042452346306560|166153499473114485266460341390278656"
def inputClause3563 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,false),(60,true)]
theorem inputList3563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3563 (by decide) v hb
mask_input "3563|9042387921797120|166153499473114485266460405814788096"
def inputClause3564 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,true),(53,false),(60,true)]
theorem inputList3564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3564 (by decide) v hb
mask_input "3564|9042383626829824|166153499473114485266460410109755392"
def inputClause3565 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,false),(60,true)]
theorem inputList3565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3565 (by decide) v hb
mask_input "3565|9007272269185024|166153499473114485266495521467400192"
def inputClause3566 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,true),(53,false),(60,true)]
theorem inputList3566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3566 (by decide) v hb
mask_input "3566|9007267974217728|166153499473114485266495525762367488"
def inputClause3567 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(53,false),(60,true)]
theorem inputList3567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3567 (by decide) v hb
mask_input "3567|9007203549708288|166153499473114485266495590186876928"
def inputClause3568 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,false),(60,true)]
theorem inputList3568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3568 (by decide) v hb
mask_input "3568|166153499473114484121983081789784064|1153519711946801152"
def inputClause3569 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,false),(53,true),(60,true)]
theorem inputList3569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3569 (by decide) v hb
mask_input "3569|598207339954176|166153499473114485274904586396631040"
def inputClause3570 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(53,true),(60,true)]
theorem inputList3570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3570 (by decide) v hb
mask_input "3570|598203044986880|166153499473114485274904590691598336"
def inputClause3571 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,true),(60,true)]
theorem inputList3571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3571 (by decide) v hb
mask_input "3571|598138620477440|166153499473114485274904655116107776"
def inputClause3572 : CNF.NClause := [(117,true),(32,true),(36,true),(45,false),(49,false),(53,true),(60,true)]
theorem inputList3572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3572 (by decide) v hb
mask_input "3572|598134325510144|166153499473114485274904659411075072"
def inputClause3573 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,false),(53,true),(60,true)]
theorem inputList3573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3573 (by decide) v hb
mask_input "3573|563022967865344|166153499473114485274939770768719872"
def inputClause3574 : CNF.NClause := [(117,true),(32,true),(36,false),(45,true),(49,false),(53,true),(60,true)]
theorem inputList3574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3574 (by decide) v hb
mask_input "3574|563018672898048|166153499473114485274939775063687168"
def inputClause3575 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,true),(60,true)]
theorem inputList3575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3575 (by decide) v hb
mask_input "3575|562954248388608|166153499473114485274939839488196608"
def inputClause3577 : CNF.NClause := [(117,true),(32,false),(36,false),(45,false),(49,true),(53,true),(60,true)]
theorem inputList3577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3577 (by decide) v hb
mask_input "3577|35257386532864|166153499473114485275467536350052352"
def inputClause3578 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,true),(53,true),(60,true)]
theorem inputList3578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3578 (by decide) v hb
mask_input "3578|35253091565568|166153499473114485275467540645019648"
def inputClause3579 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,true),(53,true),(60,true)]
theorem inputList3579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3579 (by decide) v hb
mask_input "3579|35188667056128|166153499473114485275467605069529088"
def inputClause3581 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(53,true),(60,true)]
theorem inputList3581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3581 (by decide) v hb
mask_input "3581|73014444032|166153499473114485275502720722141184"
def inputClause3584 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,true),(60,true)]
theorem inputList3584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3584 (by decide) v hb
mask_input "3584|166153499473114484112975882535043072|1162526911201542144"
def inputClause3585 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,false),(35,false),(61,false)]
theorem inputList3585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3585 (by decide) v hb
mask_input "3585|2305843075785687040|332306998946228968225951765070086144"
def inputClause3587 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,false),(35,false),(61,false)]
theorem inputList3587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3587 (by decide) v hb
mask_input "3587|2305843071490719744|332306998946228968225951769365053440"
def inputClause3588 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,false),(61,false)]
theorem inputList3588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3588 (by decide) v hb
mask_input "3588|2305843069343236096|332306998946228968225951771512537088"
def inputClause3589 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,false),(61,false)]
theorem inputList3589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3589 (by decide) v hb
mask_input "3589|2305843067195752448|332306998946228968225951773660020736"
def inputClause3590 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,false),(61,false)]
theorem inputList3590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3590 (by decide) v hb
mask_input "3590|2305843065048268800|332306998946228968225951775807504384"
def inputClause3591 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,false),(61,false)]
theorem inputList3591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3591 (by decide) v hb
mask_input "3591|2305843062900785152|332306998946228968225951777954988032"
def inputClause3592 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,false),(61,false)]
theorem inputList3592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3592 (by decide) v hb
mask_input "3592|2305843060753301504|332306998946228968225951780102471680"
def inputClause3593 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,false),(61,false)]
theorem inputList3593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3593 (by decide) v hb
mask_input "3593|2305843058605817856|332306998946228968225951782249955328"
def inputClause3594 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,false),(61,false)]
theorem inputList3594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3594 (by decide) v hb
mask_input "3594|2305843056458334208|332306998946228968225951784397438976"
def inputClause3595 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,false),(61,false)]
theorem inputList3595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3595 (by decide) v hb
mask_input "3595|2305843054310850560|332306998946228968225951786544922624"
def inputClause3596 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,true),(35,false),(61,false)]
theorem inputList3596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3596 (by decide) v hb
mask_input "3596|2305843052163366912|332306998946228968225951788692406272"
def inputClause3597 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,false),(61,false)]
theorem inputList3597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3597 (by decide) v hb
mask_input "3597|2305843050015883264|332306998946228968225951790839889920"
def inputClause3598 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,false),(61,false)]
theorem inputList3598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3598 (by decide) v hb
mask_input "3598|2305843047868399616|332306998946228968225951792987373568"
def inputClause3599 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(35,false),(61,false)]
theorem inputList3599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3599 (by decide) v hb
mask_input "3599|2305843045720915968|332306998946228968225951795134857216"
end Percolation.MaskChain
