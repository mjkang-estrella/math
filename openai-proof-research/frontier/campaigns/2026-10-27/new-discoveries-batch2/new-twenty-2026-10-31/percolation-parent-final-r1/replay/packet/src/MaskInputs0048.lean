import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2637 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,false),(61,false)]
theorem inputList2637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2637 (by decide) v hb
mask_input "2637|2305884790655549440|10141204801825835238361904709632"
def inputClause2638 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,true),(45,false),(61,false)]
theorem inputList2638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2638 (by decide) v hb
mask_input "2638|2305882591632293888|10141204801825835240560927965184"
def inputClause2639 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,true),(45,false),(61,false)]
theorem inputList2639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2639 (by decide) v hb
mask_input "2639|2305880392609038336|10141204801825835242759951220736"
def inputClause2640 : CNF.NClause := [(103,true),(41,true),(42,true),(43,true),(44,true),(45,false),(61,false)]
theorem inputList2640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2640 (by decide) v hb
mask_input "2640|2305878193585782784|10141204801825835244958974476288"
def inputClause2641 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,true),(61,false)]
theorem inputList2641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2641 (by decide) v hb
mask_input "2641|2305875994562527232|10141204801825835247157997731840"
def inputClause2642 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,true),(61,false)]
theorem inputList2642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2642 (by decide) v hb
mask_input "2642|2305873795539271680|10141204801825835249357020987392"
def inputClause2643 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,true),(61,false)]
theorem inputList2643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2643 (by decide) v hb
mask_input "2643|2305871596516016128|10141204801825835251556044242944"
def inputClause2645 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,true),(61,false)]
theorem inputList2645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2645 (by decide) v hb
mask_input "2645|2305867198469505024|10141204801825835255954090754048"
def inputClause2646 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,true),(61,false)]
theorem inputList2646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2646 (by decide) v hb
mask_input "2646|2305864999446249472|10141204801825835258153114009600"
def inputClause2647 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,true),(61,false)]
theorem inputList2647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2647 (by decide) v hb
mask_input "2647|2305862800422993920|10141204801825835260352137265152"
def inputClause2649 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,true),(61,false)]
theorem inputList2649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2649 (by decide) v hb
mask_input "2649|2305858402376482816|10141204801825835264750183776256"
def inputClause2650 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,true),(61,false)]
theorem inputList2650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2650 (by decide) v hb
mask_input "2650|2305856203353227264|10141204801825835266949207031808"
def inputClause2651 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,true),(61,false)]
theorem inputList2651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2651 (by decide) v hb
mask_input "2651|2305854004329971712|10141204801825835269148230287360"
def inputClause2653 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,true),(61,false)]
theorem inputList2653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2653 (by decide) v hb
mask_input "2653|2305849606283460608|10141204801825835273546276798464"
def inputClause2655 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,true),(45,true),(61,false)]
theorem inputList2655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2655 (by decide) v hb
mask_input "2655|2305845208236949504|10141204801825835277944323309568"
def inputClause2657 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,false),(61,true)]
theorem inputList2657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2657 (by decide) v hb
mask_input "2657|68169720922112|10141204801828141054982839336960"
def inputClause2658 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,false),(61,true)]
theorem inputList2658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2658 (by decide) v hb
mask_input "2658|65970697666560|10141204801828141057181862592512"
def inputClause2659 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,false),(61,true)]
theorem inputList2659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2659 (by decide) v hb
mask_input "2659|63771674411008|10141204801828141059380885848064"
def inputClause2660 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,false),(61,true)]
theorem inputList2660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2660 (by decide) v hb
mask_input "2660|61572651155456|10141204801828141061579909103616"
def inputClause2661 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,false),(61,true)]
theorem inputList2661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2661 (by decide) v hb
mask_input "2661|59373627899904|10141204801828141063778932359168"
def inputClause2662 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,false),(61,true)]
theorem inputList2662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2662 (by decide) v hb
mask_input "2662|57174604644352|10141204801828141065977955614720"
def inputClause2663 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,false),(61,true)]
theorem inputList2663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2663 (by decide) v hb
mask_input "2663|54975581388800|10141204801828141068176978870272"
def inputClause2664 : CNF.NClause := [(103,true),(41,true),(42,true),(43,true),(44,false),(45,false),(61,true)]
theorem inputList2664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2664 (by decide) v hb
mask_input "2664|52776558133248|10141204801828141070376002125824"
def inputClause2665 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,false),(61,true)]
theorem inputList2665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2665 (by decide) v hb
mask_input "2665|50577534877696|10141204801828141072575025381376"
def inputClause2666 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,false),(61,true)]
theorem inputList2666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2666 (by decide) v hb
mask_input "2666|48378511622144|10141204801828141074774048636928"
def inputClause2667 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,false),(61,true)]
theorem inputList2667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2667 (by decide) v hb
mask_input "2667|46179488366592|10141204801828141076973071892480"
def inputClause2668 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,true),(45,false),(61,true)]
theorem inputList2668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2668 (by decide) v hb
mask_input "2668|43980465111040|10141204801828141079172095148032"
def inputClause2669 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,false),(61,true)]
theorem inputList2669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2669 (by decide) v hb
mask_input "2669|41781441855488|10141204801828141081371118403584"
def inputClause2670 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,true),(45,false),(61,true)]
theorem inputList2670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2670 (by decide) v hb
mask_input "2670|39582418599936|10141204801828141083570141659136"
def inputClause2671 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,true),(45,false),(61,true)]
theorem inputList2671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2671 (by decide) v hb
mask_input "2671|37383395344384|10141204801828141085769164914688"
def inputClause2673 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,true),(61,true)]
theorem inputList2673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2673 (by decide) v hb
mask_input "2673|32985348833280|10141204801828141090167211425792"
def inputClause2674 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,true),(61,true)]
theorem inputList2674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2674 (by decide) v hb
mask_input "2674|30786325577728|10141204801828141092366234681344"
def inputClause2675 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,true),(61,true)]
theorem inputList2675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2675 (by decide) v hb
mask_input "2675|28587302322176|10141204801828141094565257936896"
def inputClause2676 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,true),(61,true)]
theorem inputList2676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2676 (by decide) v hb
mask_input "2676|26388279066624|10141204801828141096764281192448"
def inputClause2677 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,true),(61,true)]
theorem inputList2677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2677 (by decide) v hb
mask_input "2677|24189255811072|10141204801828141098963304448000"
def inputClause2678 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,true),(61,true)]
theorem inputList2678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2678 (by decide) v hb
mask_input "2678|21990232555520|10141204801828141101162327703552"
def inputClause2679 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,true),(61,true)]
theorem inputList2679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2679 (by decide) v hb
mask_input "2679|19791209299968|10141204801828141103361350959104"
def inputClause2681 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,true),(61,true)]
theorem inputList2681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2681 (by decide) v hb
mask_input "2681|15393162788864|10141204801828141107759397470208"
def inputClause2682 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,true),(61,true)]
theorem inputList2682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2682 (by decide) v hb
mask_input "2682|13194139533312|10141204801828141109958420725760"
def inputClause2683 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,true),(61,true)]
theorem inputList2683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2683 (by decide) v hb
mask_input "2683|10995116277760|10141204801828141112157443981312"
end Percolation.MaskChain
