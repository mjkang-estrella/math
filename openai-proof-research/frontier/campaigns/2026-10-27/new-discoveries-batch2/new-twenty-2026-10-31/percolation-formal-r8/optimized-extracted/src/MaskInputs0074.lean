import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3791 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,true),(53,false),(59,false)]
theorem inputList3791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3791 (by decide) v hb
mask_input "3791|585467953705648128|2658455991569831745808744968269856768"
def inputClause3792 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,true),(53,false),(59,false)]
theorem inputList3792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3792 (by decide) v hb
mask_input "3792|585467951558164480|2658455991569831745808744970417340416"
def inputClause3793 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,true),(59,false)]
theorem inputList3793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3793 (by decide) v hb
mask_input "3793|577591602160074752|2658455991569831745816621319815430144"
def inputClause3794 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,true),(59,false)]
theorem inputList3794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3794 (by decide) v hb
mask_input "3794|577591600012591104|2658455991569831745816621321962913792"
def inputClause3795 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,true),(59,false)]
theorem inputList3795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3795 (by decide) v hb
mask_input "3795|577591052404260864|2658455991569831745816621869571244032"
def inputClause3796 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,true),(59,false)]
theorem inputList3796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3796 (by decide) v hb
mask_input "3796|577591050256777216|2658455991569831745816621871718727680"
def inputClause3797 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,true),(59,false)]
theorem inputList3797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3797 (by decide) v hb
mask_input "3797|577587204113563648|2658455991569831745816625717861941248"
def inputClause3798 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,true),(59,false)]
theorem inputList3798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3798 (by decide) v hb
mask_input "3798|577587201966080000|2658455991569831745816625720009424896"
def inputClause3799 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,true),(59,false)]
theorem inputList3799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3799 (by decide) v hb
mask_input "3799|577586654357749760|2658455991569831745816626267617755136"
def inputClause3800 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,false),(53,true),(59,false)]
theorem inputList3800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3800 (by decide) v hb
mask_input "3800|577586652210266112|2658455991569831745816626269765238784"
def inputClause3801 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,true),(59,false)]
theorem inputList3801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3801 (by decide) v hb
mask_input "3801|576465702253232128|2658455991569831745817747219722272768"
def inputClause3802 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,true),(59,false)]
theorem inputList3802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3802 (by decide) v hb
mask_input "3802|576465700105748480|2658455991569831745817747221869756416"
def inputClause3803 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,true),(59,false)]
theorem inputList3803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3803 (by decide) v hb
mask_input "3803|576465152497418240|2658455991569831745817747769478086656"
def inputClause3804 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,true),(53,true),(59,false)]
theorem inputList3804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3804 (by decide) v hb
mask_input "3804|576465150349934592|2658455991569831745817747771625570304"
def inputClause3805 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,true),(59,false)]
theorem inputList3805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3805 (by decide) v hb
mask_input "3805|576461304206721024|2658455991569831745817751617768783872"
def inputClause3806 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,true),(53,true),(59,false)]
theorem inputList3806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3806 (by decide) v hb
mask_input "3806|576461302059237376|2658455991569831745817751619916267520"
def inputClause3808 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,true),(53,true),(59,false)]
theorem inputList3808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3808 (by decide) v hb
mask_input "3808|2658455991569831746384074872864112640|10138049111392256"
def inputClause3809 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,false),(59,true)]
theorem inputList3809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3809 (by decide) v hb
mask_input "3809|10138049111392256|2658455991569831746384074872864112640"
def inputClause3810 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,false),(59,true)]
theorem inputList3810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3810 (by decide) v hb
mask_input "3810|10138046963908608|2658455991569831746384074875011596288"
def inputClause3811 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,false),(59,true)]
theorem inputList3811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3811 (by decide) v hb
mask_input "3811|10137499355578368|2658455991569831746384075422619926528"
def inputClause3812 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,false),(59,true)]
theorem inputList3812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3812 (by decide) v hb
mask_input "3812|10137497208094720|2658455991569831746384075424767410176"
def inputClause3813 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,false),(59,true)]
theorem inputList3813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3813 (by decide) v hb
mask_input "3813|10133651064881152|2658455991569831746384079270910623744"
def inputClause3814 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,false),(59,true)]
theorem inputList3814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3814 (by decide) v hb
mask_input "3814|10133648917397504|2658455991569831746384079273058107392"
def inputClause3815 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,false),(59,true)]
theorem inputList3815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3815 (by decide) v hb
mask_input "3815|10133101309067264|2658455991569831746384079820666437632"
def inputClause3816 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,false),(53,false),(59,true)]
theorem inputList3816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3816 (by decide) v hb
mask_input "3816|10133099161583616|2658455991569831746384079822813921280"
def inputClause3817 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,false),(59,true)]
theorem inputList3817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3817 (by decide) v hb
mask_input "3817|9012149204549632|2658455991569831746385200772770955264"
def inputClause3818 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,false),(59,true)]
theorem inputList3818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3818 (by decide) v hb
mask_input "3818|9012147057065984|2658455991569831746385200774918438912"
def inputClause3819 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,false),(59,true)]
theorem inputList3819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3819 (by decide) v hb
mask_input "3819|9011599448735744|2658455991569831746385201322526769152"
def inputClause3820 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,true),(53,false),(59,true)]
theorem inputList3820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3820 (by decide) v hb
mask_input "3820|9011597301252096|2658455991569831746385201324674252800"
def inputClause3821 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,false),(59,true)]
theorem inputList3821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3821 (by decide) v hb
mask_input "3821|9007751158038528|2658455991569831746385205170817466368"
def inputClause3822 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,true),(53,false),(59,true)]
theorem inputList3822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3822 (by decide) v hb
mask_input "3822|9007749010554880|2658455991569831746385205172964950016"
def inputClause3823 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,true),(53,false),(59,true)]
theorem inputList3823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3823 (by decide) v hb
mask_input "3823|9007201402224640|2658455991569831746385205720573280256"
def inputClause3824 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,true),(53,false),(59,true)]
theorem inputList3824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3824 (by decide) v hb
mask_input "3824|2658455991569831745816621319815430144|577591602160074752"
def inputClause3825 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,true),(59,true)]
theorem inputList3825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3825 (by decide) v hb
mask_input "3825|1130849856651264|2658455991569831746393082072118853632"
def inputClause3826 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,true),(59,true)]
theorem inputList3826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3826 (by decide) v hb
mask_input "3826|1130847709167616|2658455991569831746393082074266337280"
def inputClause3827 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,true),(59,true)]
theorem inputList3827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3827 (by decide) v hb
mask_input "3827|1130300100837376|2658455991569831746393082621874667520"
def inputClause3828 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,true),(59,true)]
theorem inputList3828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3828 (by decide) v hb
mask_input "3828|1130297953353728|2658455991569831746393082624022151168"
def inputClause3829 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,true),(59,true)]
theorem inputList3829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3829 (by decide) v hb
mask_input "3829|1126451810140160|2658455991569831746393086470165364736"
def inputClause3830 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,true),(59,true)]
theorem inputList3830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3830 (by decide) v hb
mask_input "3830|1126449662656512|2658455991569831746393086472312848384"
def inputClause3831 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,true),(59,true)]
theorem inputList3831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3831 (by decide) v hb
mask_input "3831|1125902054326272|2658455991569831746393087019921178624"
end Percolation.MaskChain
