import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2685 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,true),(45,true),(61,true)]
theorem inputList2685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2685 (by decide) v hb
mask_input "2685|6597069766656|10141204801828141116555490492416"
def inputClause2687 : CNF.NClause := [(103,false),(41,false),(42,true),(43,true),(44,true),(45,true),(61,true)]
theorem inputList2687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2687 (by decide) v hb
mask_input "2687|10141204801825835214172648898560|2305908979911360512"
def inputClause2688 : CNF.NClause := [(103,false),(41,true),(42,true),(43,true),(44,true),(45,true),(61,true)]
theorem inputList2688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2688 (by decide) v hb
mask_input "2688|10141204801825835211973625643008|2305911178934616064"
def inputClause2689 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,false),(59,false)]
theorem inputList2689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2689 (by decide) v hb
mask_input "2689|581529810145116160|20282409603651670423947251286016"
def inputClause2690 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,false),(59,false)]
theorem inputList2690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2690 (by decide) v hb
mask_input "2690|581529775785377792|20282409603651670423981611024384"
def inputClause2691 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,false),(59,false)]
theorem inputList2691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2691 (by decide) v hb
mask_input "2691|581529535267209216|20282409603651670424222129192960"
def inputClause2692 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,false),(59,false)]
theorem inputList2692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2692 (by decide) v hb
mask_input "2692|581529500907470848|20282409603651670424256488931328"
def inputClause2693 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,false),(59,false)]
theorem inputList2693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2693 (by decide) v hb
mask_input "2693|581527611121860608|20282409603651670426146274541568"
def inputClause2694 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,false),(59,false)]
theorem inputList2694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2694 (by decide) v hb
mask_input "2694|581527576762122240|20282409603651670426180634279936"
def inputClause2695 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,false),(59,false)]
theorem inputList2695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2695 (by decide) v hb
mask_input "2695|581527336243953664|20282409603651670426421152448512"
def inputClause2696 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,false),(59,false)]
theorem inputList2696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2696 (by decide) v hb
mask_input "2696|581527301884215296|20282409603651670426455512186880"
def inputClause2697 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,false),(59,false)]
theorem inputList2697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2697 (by decide) v hb
mask_input "2697|580966860191694848|20282409603651670986897204707328"
def inputClause2698 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,false),(59,false)]
theorem inputList2698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2698 (by decide) v hb
mask_input "2698|580966825831956480|20282409603651670986931564445696"
def inputClause2699 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,false),(59,false)]
theorem inputList2699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2699 (by decide) v hb
mask_input "2699|580966585313787904|20282409603651670987172082614272"
def inputClause2700 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,false),(59,false)]
theorem inputList2700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2700 (by decide) v hb
mask_input "2700|580966550954049536|20282409603651670987206442352640"
def inputClause2701 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,false),(59,false)]
theorem inputList2701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2701 (by decide) v hb
mask_input "2701|580964661168439296|20282409603651670989096227962880"
def inputClause2702 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,true),(52,false),(59,false)]
theorem inputList2702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2702 (by decide) v hb
mask_input "2702|580964626808700928|20282409603651670989130587701248"
def inputClause2703 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,true),(52,false),(59,false)]
theorem inputList2703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2703 (by decide) v hb
mask_input "2703|580964386290532352|20282409603651670989371105869824"
def inputClause2704 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,true),(52,false),(59,false)]
theorem inputList2704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2704 (by decide) v hb
mask_input "2704|580964351930793984|20282409603651670989405465608192"
def inputClause2705 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,true),(59,false)]
theorem inputList2705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2705 (by decide) v hb
mask_input "2705|577026210517745664|20282409603651674927546878656512"
def inputClause2706 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,true),(59,false)]
theorem inputList2706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2706 (by decide) v hb
mask_input "2706|577026176158007296|20282409603651674927581238394880"
def inputClause2707 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,true),(59,false)]
theorem inputList2707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2707 (by decide) v hb
mask_input "2707|577025935639838720|20282409603651674927821756563456"
def inputClause2708 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,true),(59,false)]
theorem inputList2708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2708 (by decide) v hb
mask_input "2708|577025901280100352|20282409603651674927856116301824"
def inputClause2709 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,true),(59,false)]
theorem inputList2709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2709 (by decide) v hb
mask_input "2709|577024011494490112|20282409603651674929745901912064"
def inputClause2710 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,true),(59,false)]
theorem inputList2710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2710 (by decide) v hb
mask_input "2710|577023977134751744|20282409603651674929780261650432"
def inputClause2711 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,true),(59,false)]
theorem inputList2711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2711 (by decide) v hb
mask_input "2711|577023736616583168|20282409603651674930020779819008"
def inputClause2712 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,true),(59,false)]
theorem inputList2712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2712 (by decide) v hb
mask_input "2712|577023702256844800|20282409603651674930055139557376"
def inputClause2713 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,true),(59,false)]
theorem inputList2713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2713 (by decide) v hb
mask_input "2713|576463260564324352|20282409603651675490496832077824"
def inputClause2714 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,true),(59,false)]
theorem inputList2714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2714 (by decide) v hb
mask_input "2714|576463226204585984|20282409603651675490531191816192"
def inputClause2715 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,true),(59,false)]
theorem inputList2715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2715 (by decide) v hb
mask_input "2715|576462985686417408|20282409603651675490771709984768"
def inputClause2716 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,true),(59,false)]
theorem inputList2716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2716 (by decide) v hb
mask_input "2716|576462951326679040|20282409603651675490806069723136"
def inputClause2717 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,true),(59,false)]
theorem inputList2717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2717 (by decide) v hb
mask_input "2717|576461061541068800|20282409603651675492695855333376"
def inputClause2718 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,true),(52,true),(59,false)]
theorem inputList2718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2718 (by decide) v hb
mask_input "2718|576461027181330432|20282409603651675492730215071744"
def inputClause2719 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,true),(52,true),(59,false)]
theorem inputList2719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2719 (by decide) v hb
mask_input "2719|576460786663161856|20282409603651675492970733240320"
def inputClause2721 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,false),(59,true)]
theorem inputList2721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2721 (by decide) v hb
mask_input "2721|5069057841692672|20282409603652246884699554709504"
def inputClause2722 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,false),(59,true)]
theorem inputList2722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2722 (by decide) v hb
mask_input "2722|5069023481954304|20282409603652246884733914447872"
def inputClause2723 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,false),(59,true)]
theorem inputList2723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2723 (by decide) v hb
mask_input "2723|5068782963785728|20282409603652246884974432616448"
def inputClause2724 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,false),(59,true)]
theorem inputList2724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2724 (by decide) v hb
mask_input "2724|5068748604047360|20282409603652246885008792354816"
def inputClause2725 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,false),(59,true)]
theorem inputList2725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2725 (by decide) v hb
mask_input "2725|5066858818437120|20282409603652246886898577965056"
def inputClause2726 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,false),(59,true)]
theorem inputList2726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2726 (by decide) v hb
mask_input "2726|5066824458698752|20282409603652246886932937703424"
end Percolation.MaskChain
