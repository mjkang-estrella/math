import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2727 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,false),(59,true)]
theorem inputList2727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2727 (by decide) v hb
mask_input "2727|5066583940530176|20282409603652246887173455872000"
def inputClause2728 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,false),(59,true)]
theorem inputList2728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2728 (by decide) v hb
mask_input "2728|5066549580791808|20282409603652246887207815610368"
def inputClause2729 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,false),(59,true)]
theorem inputList2729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2729 (by decide) v hb
mask_input "2729|4506107888271360|20282409603652247447649508130816"
def inputClause2730 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,false),(59,true)]
theorem inputList2730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2730 (by decide) v hb
mask_input "2730|4506073528532992|20282409603652247447683867869184"
def inputClause2731 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,false),(59,true)]
theorem inputList2731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2731 (by decide) v hb
mask_input "2731|4505833010364416|20282409603652247447924386037760"
def inputClause2732 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,false),(59,true)]
theorem inputList2732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2732 (by decide) v hb
mask_input "2732|4505798650626048|20282409603652247447958745776128"
def inputClause2733 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,false),(59,true)]
theorem inputList2733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2733 (by decide) v hb
mask_input "2733|4503908865015808|20282409603652247449848531386368"
def inputClause2734 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,true),(52,false),(59,true)]
theorem inputList2734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2734 (by decide) v hb
mask_input "2734|4503874505277440|20282409603652247449882891124736"
def inputClause2735 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,true),(52,false),(59,true)]
theorem inputList2735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2735 (by decide) v hb
mask_input "2735|4503633987108864|20282409603652247450123409293312"
def inputClause2737 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,false),(52,true),(59,true)]
theorem inputList2737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2737 (by decide) v hb
mask_input "2737|565458214322176|20282409603652251388299182080000"
def inputClause2738 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,false),(52,true),(59,true)]
theorem inputList2738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2738 (by decide) v hb
mask_input "2738|565423854583808|20282409603652251388333541818368"
def inputClause2739 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,true),(59,true)]
theorem inputList2739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2739 (by decide) v hb
mask_input "2739|565183336415232|20282409603652251388574059986944"
def inputClause2740 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,true),(59,true)]
theorem inputList2740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2740 (by decide) v hb
mask_input "2740|565148976676864|20282409603652251388608419725312"
def inputClause2741 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,true),(59,true)]
theorem inputList2741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2741 (by decide) v hb
mask_input "2741|563259191066624|20282409603652251390498205335552"
def inputClause2742 : CNF.NClause := [(104,true),(35,true),(38,false),(41,true),(49,false),(52,true),(59,true)]
theorem inputList2742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2742 (by decide) v hb
mask_input "2742|563224831328256|20282409603652251390532565073920"
def inputClause2743 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,true),(59,true)]
theorem inputList2743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2743 (by decide) v hb
mask_input "2743|562984313159680|20282409603652251390773083242496"
def inputClause2745 : CNF.NClause := [(104,true),(35,false),(38,false),(41,false),(49,true),(52,true),(59,true)]
theorem inputList2745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2745 (by decide) v hb
mask_input "2745|2508260900864|20282409603652251951249135501312"
def inputClause2746 : CNF.NClause := [(104,true),(35,true),(38,false),(41,false),(49,true),(52,true),(59,true)]
theorem inputList2746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2746 (by decide) v hb
mask_input "2746|2473901162496|20282409603652251951283495239680"
def inputClause2747 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,true),(52,true),(59,true)]
theorem inputList2747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2747 (by decide) v hb
mask_input "2747|2233382993920|20282409603652251951524013408256"
def inputClause2749 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,true),(52,true),(59,true)]
theorem inputList2749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2749 (by decide) v hb
mask_input "2749|309237645312|20282409603652251953448158756864"
def inputClause2751 : CNF.NClause := [(104,false),(35,false),(38,true),(41,true),(49,true),(52,true),(59,true)]
theorem inputList2751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2751 (by decide) v hb
mask_input "2751|20282409603651670423981611024384|581529775785377792"
def inputClause2752 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,true),(52,true),(59,true)]
theorem inputList2752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2752 (by decide) v hb
mask_input "2752|20282409603651670423947251286016|581529810145116160"
def inputClause2753 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,false),(60,false)]
theorem inputList2753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2753 (by decide) v hb
mask_input "2753|1172064148075315200|40564819207303340847894502572032"
def inputClause2754 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,false),(60,false)]
theorem inputList2754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2754 (by decide) v hb
mask_input "2754|1172064139485380608|40564819207303340847903092506624"
def inputClause2755 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,false),(60,false)]
theorem inputList2755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2755 (by decide) v hb
mask_input "2755|1172064010636361728|40564819207303340848031941525504"
def inputClause2756 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,false),(60,false)]
theorem inputList2756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2756 (by decide) v hb
mask_input "2756|1172064002046427136|40564819207303340848040531460096"
def inputClause2757 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,false),(60,false)]
theorem inputList2757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2757 (by decide) v hb
mask_input "2757|1172061949052059648|40564819207303340850093525827584"
def inputClause2758 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,false),(60,false)]
theorem inputList2758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2758 (by decide) v hb
mask_input "2758|1172061940462125056|40564819207303340850102115762176"
def inputClause2759 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,false),(60,false)]
theorem inputList2759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2759 (by decide) v hb
mask_input "2759|1172061811613106176|40564819207303340850230964781056"
def inputClause2760 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,false),(54,false),(60,false)]
theorem inputList2760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2760 (by decide) v hb
mask_input "2760|1172061803023171584|40564819207303340850239554715648"
def inputClause2761 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,false),(60,false)]
theorem inputList2761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2761 (by decide) v hb
mask_input "2761|1170938248168472576|40564819207303341973794409414656"
def inputClause2762 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,false),(60,false)]
theorem inputList2762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2762 (by decide) v hb
mask_input "2762|1170938239578537984|40564819207303341973802999349248"
def inputClause2763 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,false),(60,false)]
theorem inputList2763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2763 (by decide) v hb
mask_input "2763|1170938110729519104|40564819207303341973931848368128"
def inputClause2764 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,true),(54,false),(60,false)]
theorem inputList2764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2764 (by decide) v hb
mask_input "2764|1170938102139584512|40564819207303341973940438302720"
def inputClause2765 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,false),(60,false)]
theorem inputList2765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2765 (by decide) v hb
mask_input "2765|1170936049145217024|40564819207303341975993432670208"
def inputClause2766 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,true),(54,false),(60,false)]
theorem inputList2766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2766 (by decide) v hb
mask_input "2766|1170936040555282432|40564819207303341976002022604800"
def inputClause2767 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,false),(60,false)]
theorem inputList2767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2767 (by decide) v hb
mask_input "2767|1170935911706263552|40564819207303341976130871623680"
def inputClause2768 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,true),(54,false),(60,false)]
theorem inputList2768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2768 (by decide) v hb
mask_input "2768|1170935903116328960|40564819207303341976139461558272"
def inputClause2769 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,true),(60,false)]
theorem inputList2769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2769 (by decide) v hb
mask_input "2769|1154049749565833216|40564819207303358862293012054016"
def inputClause2770 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,true),(60,false)]
theorem inputList2770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2770 (by decide) v hb
mask_input "2770|1154049740975898624|40564819207303358862301601988608"
end Percolation.MaskChain
