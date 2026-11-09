import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2771 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,true),(60,false)]
theorem inputList2771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2771 (by decide) v hb
mask_input "2771|1154049612126879744|40564819207303358862430451007488"
def inputClause2772 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,true),(60,false)]
theorem inputList2772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2772 (by decide) v hb
mask_input "2772|1154049603536945152|40564819207303358862439040942080"
def inputClause2773 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,true),(60,false)]
theorem inputList2773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2773 (by decide) v hb
mask_input "2773|1154047550542577664|40564819207303358864492035309568"
def inputClause2774 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,true),(60,false)]
theorem inputList2774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2774 (by decide) v hb
mask_input "2774|1154047541952643072|40564819207303358864500625244160"
def inputClause2775 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,true),(60,false)]
theorem inputList2775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2775 (by decide) v hb
mask_input "2775|1154047413103624192|40564819207303358864629474263040"
def inputClause2776 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,false),(54,true),(60,false)]
theorem inputList2776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2776 (by decide) v hb
mask_input "2776|1154047404513689600|40564819207303358864638064197632"
def inputClause2777 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,true),(60,false)]
theorem inputList2777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2777 (by decide) v hb
mask_input "2777|1152923849658990592|40564819207303359988192918896640"
def inputClause2778 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,true),(60,false)]
theorem inputList2778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2778 (by decide) v hb
mask_input "2778|1152923841069056000|40564819207303359988201508831232"
def inputClause2779 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,true),(60,false)]
theorem inputList2779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2779 (by decide) v hb
mask_input "2779|1152923712220037120|40564819207303359988330357850112"
def inputClause2780 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,true),(54,true),(60,false)]
theorem inputList2780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2780 (by decide) v hb
mask_input "2780|1152923703630102528|40564819207303359988338947784704"
def inputClause2781 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,true),(60,false)]
theorem inputList2781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2781 (by decide) v hb
mask_input "2781|1152921650635735040|40564819207303359990391942152192"
def inputClause2782 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,true),(54,true),(60,false)]
theorem inputList2782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2782 (by decide) v hb
mask_input "2782|1152921642045800448|40564819207303359990400532086784"
def inputClause2783 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,true),(60,false)]
theorem inputList2783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2783 (by decide) v hb
mask_input "2783|1152921513196781568|40564819207303359990529381105664"
def inputClause2784 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,true),(54,true),(60,false)]
theorem inputList2784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2784 (by decide) v hb
mask_input "2784|40564819207304493769399109419008|19142643468468224"
def inputClause2785 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,false),(60,true)]
theorem inputList2785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2785 (by decide) v hb
mask_input "2785|19142643468468224|40564819207304493769399109419008"
def inputClause2786 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,false),(60,true)]
theorem inputList2786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2786 (by decide) v hb
mask_input "2786|19142634878533632|40564819207304493769407699353600"
def inputClause2787 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,false),(60,true)]
theorem inputList2787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2787 (by decide) v hb
mask_input "2787|19142506029514752|40564819207304493769536548372480"
def inputClause2788 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,false),(60,true)]
theorem inputList2788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2788 (by decide) v hb
mask_input "2788|19142497439580160|40564819207304493769545138307072"
def inputClause2789 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,false),(60,true)]
theorem inputList2789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2789 (by decide) v hb
mask_input "2789|19140444445212672|40564819207304493771598132674560"
def inputClause2790 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,false),(60,true)]
theorem inputList2790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2790 (by decide) v hb
mask_input "2790|19140435855278080|40564819207304493771606722609152"
def inputClause2791 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,false),(60,true)]
theorem inputList2791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2791 (by decide) v hb
mask_input "2791|19140307006259200|40564819207304493771735571628032"
def inputClause2792 : CNF.NClause := [(105,true),(33,true),(37,true),(41,true),(50,false),(54,false),(60,true)]
theorem inputList2792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2792 (by decide) v hb
mask_input "2792|19140298416324608|40564819207304493771744161562624"
def inputClause2793 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,false),(60,true)]
theorem inputList2793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2793 (by decide) v hb
mask_input "2793|18016743561625600|40564819207304494895299016261632"
def inputClause2794 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,false),(60,true)]
theorem inputList2794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2794 (by decide) v hb
mask_input "2794|18016734971691008|40564819207304494895307606196224"
def inputClause2795 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,false),(60,true)]
theorem inputList2795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2795 (by decide) v hb
mask_input "2795|18016606122672128|40564819207304494895436455215104"
def inputClause2796 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,true),(54,false),(60,true)]
theorem inputList2796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2796 (by decide) v hb
mask_input "2796|18016597532737536|40564819207304494895445045149696"
def inputClause2797 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,false),(60,true)]
theorem inputList2797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2797 (by decide) v hb
mask_input "2797|18014544538370048|40564819207304494897498039517184"
def inputClause2798 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,true),(54,false),(60,true)]
theorem inputList2798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2798 (by decide) v hb
mask_input "2798|18014535948435456|40564819207304494897506629451776"
def inputClause2799 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,false),(60,true)]
theorem inputList2799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2799 (by decide) v hb
mask_input "2799|18014407099416576|40564819207304494897635478470656"
def inputClause2801 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,true),(60,true)]
theorem inputList2801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2801 (by decide) v hb
mask_input "2801|1128244958986240|40564819207304511783797618900992"
def inputClause2802 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,false),(54,true),(60,true)]
theorem inputList2802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2802 (by decide) v hb
mask_input "2802|1128236369051648|40564819207304511783806208835584"
def inputClause2803 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,true),(60,true)]
theorem inputList2803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2803 (by decide) v hb
mask_input "2803|1128107520032768|40564819207304511783935057854464"
def inputClause2804 : CNF.NClause := [(105,true),(33,true),(37,true),(41,false),(50,false),(54,true),(60,true)]
theorem inputList2804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2804 (by decide) v hb
mask_input "2804|1128098930098176|40564819207304511783943647789056"
def inputClause2805 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,false),(54,true),(60,true)]
theorem inputList2805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2805 (by decide) v hb
mask_input "2805|1126045935730688|40564819207304511785996642156544"
def inputClause2806 : CNF.NClause := [(105,true),(33,true),(37,false),(41,true),(50,false),(54,true),(60,true)]
theorem inputList2806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2806 (by decide) v hb
mask_input "2806|1126037345796096|40564819207304511786005232091136"
def inputClause2807 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,false),(54,true),(60,true)]
theorem inputList2807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2807 (by decide) v hb
mask_input "2807|1125908496777216|40564819207304511786134081110016"
def inputClause2809 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,true),(54,true),(60,true)]
theorem inputList2809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2809 (by decide) v hb
mask_input "2809|2345052143616|40564819207304512909697525743616"
def inputClause2810 : CNF.NClause := [(105,true),(33,true),(37,false),(41,false),(50,true),(54,true),(60,true)]
theorem inputList2810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2810 (by decide) v hb
mask_input "2810|2336462209024|40564819207304512909706115678208"
def inputClause2811 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,true),(54,true),(60,true)]
theorem inputList2811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2811 (by decide) v hb
mask_input "2811|2207613190144|40564819207304512909834964697088"
def inputClause2813 : CNF.NClause := [(105,true),(33,false),(37,false),(41,true),(50,true),(54,true),(60,true)]
theorem inputList2813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2813 (by decide) v hb
mask_input "2813|146028888064|40564819207304512911896548999168"
end Percolation.MaskChain
