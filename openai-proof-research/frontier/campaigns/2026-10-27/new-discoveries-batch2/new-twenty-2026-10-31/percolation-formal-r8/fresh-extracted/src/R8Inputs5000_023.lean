import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5356 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5356 (by decide) v hb
mask_input "5356|47223664830895475392512|4951859326837661362145985536"
def inputClause5357 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5357 (by decide) v hb
mask_input "5357|42501298348025830179840|4951864049204144231791198208"
def inputClause5358 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5358 (by decide) v hb
mask_input "5358|42501298348025830178816|4951864049204144231791199232"
def inputClause5359 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5359 (by decide) v hb
mask_input "5359|37778931865156184966144|4951868771570627101436411904"
def inputClause5360 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5360 (by decide) v hb
mask_input "5360|37778931865156184965120|4951868771570627101436412928"
def inputClause5361 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5361 (by decide) v hb
mask_input "5361|33056565382286539752448|4951873493937109971081625600"
def inputClause5362 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5362 (by decide) v hb
mask_input "5362|33056565382286539751424|4951873493937109971081626624"
def inputClause5363 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5363 (by decide) v hb
mask_input "5363|28334198899416894538752|4951878216303592840726839296"
def inputClause5364 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5364 (by decide) v hb
mask_input "5364|28334198899416894537728|4951878216303592840726840320"
def inputClause5365 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5365 (by decide) v hb
mask_input "5365|23611832416547249325056|4951882938670075710372052992"
def inputClause5366 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5366 (by decide) v hb
mask_input "5366|23611832416547249324032|4951882938670075710372054016"
def inputClause5367 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5367 (by decide) v hb
mask_input "5367|18889465933677604111360|4951887661036558580017266688"
def inputClause5368 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inputList5368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5368 (by decide) v hb
mask_input "5368|18889465933677604110336|4951887661036558580017267712"
def inputClause5369 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inputList5369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5369 (by decide) v hb
mask_input "5369|14167099450807958897664|4951892383403041449662480384"
def inputClause5370 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inputList5370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5370 (by decide) v hb
mask_input "5370|14167099450807958896640|4951892383403041449662481408"
def inputClause5371 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inputList5371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5371 (by decide) v hb
mask_input "5371|9444732967938313683968|4951897105769524319307694080"
def inputClause5372 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inputList5372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5372 (by decide) v hb
mask_input "5372|9444732967938313682944|4951897105769524319307695104"
def inputClause5373 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inputList5373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5373 (by decide) v hb
mask_input "5373|4722366485068668470272|4951901828136007188952907776"
def inputClause5374 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inputList5374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5374 (by decide) v hb
mask_input "5374|4722366485068668469248|4951901828136007188952908800"
def inputClause5376 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inputList5376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5376 (by decide) v hb
mask_input "5376|2199023255552|4951906550502490058598122496"
def inputClause5377 : CNF.NClause := [(42,true),(11,false),(66,false),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5377 (by decide) v hb
mask_input "5377|1248825758111181460660553728|4398046511104"
def inputClause5378 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5378 (by decide) v hb
mask_input "5378|1248825758111185858707062784|2048"
def inputClause5379 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5379 (by decide) v hb
mask_input "5379|1248825684324209563868858368|73786976294838206464"
def inputClause5380 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5380 (by decide) v hb
mask_input "5380|1248825684324209563868856320|73786976294838208512"
def inputClause5381 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5381 (by decide) v hb
mask_input "5381|1248825167815375500001413120|590295810358705651712"
def inputClause5382 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5382 (by decide) v hb
mask_input "5382|1248825167815375500001411072|590295810358705653760"
def inputClause5383 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5383 (by decide) v hb
mask_input "5383|1248825094028399205163206656|664082786653543858176"
def inputClause5384 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inputList5384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5384 (by decide) v hb
mask_input "5384|1248825094028399205163204608|664082786653543860224"
def inputClause5385 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5385 (by decide) v hb
mask_input "5385|1248821035744702989061851136|4722366482869645213696"
def inputClause5386 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5386 (by decide) v hb
mask_input "5386|1248821035744702989061849088|4722366482869645215744"
def inputClause5387 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5387 (by decide) v hb
mask_input "5387|1248820961957726694223644672|4796153459164483420160"
def inputClause5388 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5388 (by decide) v hb
mask_input "5388|1248820961957726694223642624|4796153459164483422208"
def inputClause5389 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5389 (by decide) v hb
mask_input "5389|1248820445448892630356199424|5312662293228350865408"
def inputClause5390 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5390 (by decide) v hb
mask_input "5390|1248820445448892630356197376|5312662293228350867456"
def inputClause5391 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5391 (by decide) v hb
mask_input "5391|1248820371661916335517992960|5386449269523189071872"
def inputClause5392 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inputList5392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5392 (by decide) v hb
mask_input "5392|1248820371661916335517990912|5386449269523189073920"
def inputClause5393 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5393 (by decide) v hb
mask_input "5393|1247616832291571229532358656|1208925819614629174706176"
def inputClause5394 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5394 (by decide) v hb
mask_input "5394|1247616832291571229532356608|1208925819614629174708224"
def inputClause5395 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5395 (by decide) v hb
mask_input "5395|1247616758504594934694152192|1208999606590924012912640"
def inputClause5396 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5396 (by decide) v hb
mask_input "5396|1247616758504594934694150144|1208999606590924012914688"
end Percolation.MaskChain
