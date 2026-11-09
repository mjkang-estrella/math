import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5564 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5564 (by decide) v hb
mask_input "5564|2475880373718674525244096512|41108218680124335294779392"
def inputClause5565 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5565 (by decide) v hb
mask_input "5565|2475880097017513419600826368|41108495381285440938049536"
def inputClause5566 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5566 (by decide) v hb
mask_input "5566|2475880097017513419600822272|41108495381285440938053632"
def inputClause5567 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5567 (by decide) v hb
mask_input "5567|2475880078570769345891274752|41108513828029514647601152"
def inputClause5568 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,true),(91,false)]
theorem inputList5568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5568 (by decide) v hb
mask_input "5568|2475880078570769345891270656|41108513828029514647605248"
def inputClause5569 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5569 (by decide) v hb
mask_input "5569|41108513828038310740627456|2475880078570760549798248448"
def inputClause5570 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5570 (by decide) v hb
mask_input "5570|41108513828038310740623360|2475880078570760549798252544"
def inputClause5571 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5571 (by decide) v hb
mask_input "5571|41108495381294237031075840|2475880097017504623507800064"
def inputClause5572 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5572 (by decide) v hb
mask_input "5572|41108495381294237031071744|2475880097017504623507804160"
def inputClause5573 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5573 (by decide) v hb
mask_input "5573|41108218680133131387801600|2475880373718665729151074304"
def inputClause5574 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5574 (by decide) v hb
mask_input "5574|41108218680133131387797504|2475880373718665729151078400"
def inputClause5575 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5575 (by decide) v hb
mask_input "5575|41108200233389057678249984|2475880392165409802860625920"
def inputClause5576 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,false),(91,true)]
theorem inputList5576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5576 (by decide) v hb
mask_input "5576|41108200233389057678245888|2475880392165409802860630016"
def inputClause5577 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5577 (by decide) v hb
mask_input "5577|41103791461555441095413760|2475884800937243419443462144"
def inputClause5578 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5578 (by decide) v hb
mask_input "5578|41103791461555441095409664|2475884800937243419443466240"
def inputClause5579 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5579 (by decide) v hb
mask_input "5579|41103773014811367385862144|2475884819383987493153013760"
def inputClause5580 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5580 (by decide) v hb
mask_input "5580|41103773014811367385858048|2475884819383987493153017856"
def inputClause5581 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5581 (by decide) v hb
mask_input "5581|41103496313650261742587904|2475885096085148598796288000"
def inputClause5582 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5582 (by decide) v hb
mask_input "5582|41103496313650261742583808|2475885096085148598796292096"
def inputClause5583 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5583 (by decide) v hb
mask_input "5583|41103477866906188033036288|2475885114531892672505839616"
def inputClause5584 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,false),(91,true)]
theorem inputList5584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5584 (by decide) v hb
mask_input "5584|41103477866906188033032192|2475885114531892672505843712"
def inputClause5585 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5585 (by decide) v hb
mask_input "5585|38690662188809052391215104|2478297930209989808147660800"
def inputClause5586 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5586 (by decide) v hb
mask_input "5586|38690662188809052391211008|2478297930209989808147664896"
def inputClause5587 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5587 (by decide) v hb
mask_input "5587|38690643742064978681663488|2478297948656733881857212416"
def inputClause5588 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5588 (by decide) v hb
mask_input "5588|38690643742064978681659392|2478297948656733881857216512"
def inputClause5589 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5589 (by decide) v hb
mask_input "5589|38690367040903873038389248|2478298225357894987500486656"
def inputClause5590 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5590 (by decide) v hb
mask_input "5590|38690367040903873038385152|2478298225357894987500490752"
def inputClause5591 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5591 (by decide) v hb
mask_input "5591|38690348594159799328837632|2478298243804639061210038272"
def inputClause5592 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,false),(91,true)]
theorem inputList5592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5592 (by decide) v hb
mask_input "5592|38690348594159799328833536|2478298243804639061210042368"
def inputClause5593 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5593 (by decide) v hb
mask_input "5593|38685939822326182746001408|2478302652576472677792874496"
def inputClause5594 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5594 (by decide) v hb
mask_input "5594|38685939822326182745997312|2478302652576472677792878592"
def inputClause5595 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5595 (by decide) v hb
mask_input "5595|38685921375582109036449792|2478302671023216751502426112"
def inputClause5596 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5596 (by decide) v hb
mask_input "5596|38685921375582109036445696|2478302671023216751502430208"
def inputClause5597 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5597 (by decide) v hb
mask_input "5597|38685644674421003393175552|2478302947724377857145700352"
def inputClause5598 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5598 (by decide) v hb
mask_input "5598|38685644674421003393171456|2478302947724377857145704448"
def inputClause5599 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5599 (by decide) v hb
mask_input "5599|38685626227676929683623936|2478302966171121930855251968"
def inputClause5600 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,false),(91,true)]
theorem inputList5600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5600 (by decide) v hb
mask_input "5600|38685626227676929683619840|2478302966171121930855256064"
def inputClause5601 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5601 (by decide) v hb
mask_input "5601|2422887600370177150029824|2514565704798428683388846080"
def inputClause5602 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5602 (by decide) v hb
mask_input "5602|2422887600370177150025728|2514565704798428683388850176"
def inputClause5603 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5603 (by decide) v hb
mask_input "5603|2422869153626103440478208|2514565723245172757098397696"
end Percolation.MaskChain
