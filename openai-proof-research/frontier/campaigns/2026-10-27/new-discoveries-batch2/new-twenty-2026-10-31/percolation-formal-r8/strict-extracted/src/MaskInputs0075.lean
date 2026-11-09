import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3832 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,false),(53,true),(59,true)]
theorem inputList3832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3832 (by decide) v hb
mask_input "3832|2658455991569831745808740020467531776|585472901507973120"
def inputClause3833 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,true),(59,true)]
theorem inputList3833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3833 (by decide) v hb
mask_input "3833|4949949808640|2658455991569831746394207972025696256"
def inputClause3834 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,true),(59,true)]
theorem inputList3834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3834 (by decide) v hb
mask_input "3834|4947802324992|2658455991569831746394207974173179904"
def inputClause3835 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,true),(59,true)]
theorem inputList3835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3835 (by decide) v hb
mask_input "3835|4400193994752|2658455991569831746394208521781510144"
def inputClause3837 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,true),(59,true)]
theorem inputList3837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3837 (by decide) v hb
mask_input "3837|551903297536|2658455991569831746394212370072207360"
def inputClause3838 : CNF.NClause := [(121,false),(31,true),(39,false),(42,true),(50,true),(53,true),(59,true)]
theorem inputList3838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3838 (by decide) v hb
mask_input "3838|2658455991569831745807614670316503040|586598251659001856"
def inputClause3839 : CNF.NClause := [(121,false),(31,false),(39,true),(42,true),(50,true),(53,true),(59,true)]
theorem inputList3839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3839 (by decide) v hb
mask_input "3839|2658455991569831745807614122708172800|586598799267332096"
def inputClause3840 : CNF.NClause := [(121,false),(31,true),(39,true),(42,true),(50,true),(53,true),(59,true)]
theorem inputList3840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3840 (by decide) v hb
mask_input "3840|2658455991569831745807614120560689152|586598801414815744"
def inputClause3841 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,false),(57,false)]
theorem inputList3841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3841 (by decide) v hb
mask_input "3841|180715870727700480|5316911983139663491615228241121378304"
def inputClause3842 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,false),(57,false)]
theorem inputList3842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3842 (by decide) v hb
mask_input "3842|180715868580216832|5316911983139663491615228243268861952"
def inputClause3843 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,false),(57,false)]
theorem inputList3843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3843 (by decide) v hb
mask_input "3843|180715733288747008|5316911983139663491615228378560331776"
def inputClause3844 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,false),(57,false)]
theorem inputList3844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3844 (by decide) v hb
mask_input "3844|180715731141263360|5316911983139663491615228380707815424"
def inputClause3845 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(55,false),(57,false)]
theorem inputList3845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3845 (by decide) v hb
mask_input "3845|180707074634678272|5316911983139663491615237037214400512"
def inputClause3846 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,false),(57,false)]
theorem inputList3846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3846 (by decide) v hb
mask_input "3846|180707072487194624|5316911983139663491615237039361884160"
def inputClause3847 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,false),(57,false)]
theorem inputList3847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3847 (by decide) v hb
mask_input "3847|180706937195724800|5316911983139663491615237174653353984"
def inputClause3848 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,false),(55,false),(57,false)]
theorem inputList3848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3848 (by decide) v hb
mask_input "3848|180706935048241152|5316911983139663491615237176800837632"
def inputClause3849 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,false),(57,false)]
theorem inputList3849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3849 (by decide) v hb
mask_input "3849|180152920774279168|5316911983139663491615791191074799616"
def inputClause3850 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,false),(57,false)]
theorem inputList3850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3850 (by decide) v hb
mask_input "3850|180152918626795520|5316911983139663491615791193222283264"
def inputClause3851 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,true),(55,false),(57,false)]
theorem inputList3851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3851 (by decide) v hb
mask_input "3851|180152783335325696|5316911983139663491615791328513753088"
def inputClause3852 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,true),(55,false),(57,false)]
theorem inputList3852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3852 (by decide) v hb
mask_input "3852|180152781187842048|5316911983139663491615791330661236736"
def inputClause3853 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,true),(55,false),(57,false)]
theorem inputList3853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3853 (by decide) v hb
mask_input "3853|180144124681256960|5316911983139663491615799987167821824"
def inputClause3854 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,true),(55,false),(57,false)]
theorem inputList3854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3854 (by decide) v hb
mask_input "3854|180144122533773312|5316911983139663491615799989315305472"
def inputClause3855 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,true),(55,false),(57,false)]
theorem inputList3855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3855 (by decide) v hb
mask_input "3855|180143987242303488|5316911983139663491615800124606775296"
def inputClause3856 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,true),(55,false),(57,false)]
theorem inputList3856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3856 (by decide) v hb
mask_input "3856|180143985094819840|5316911983139663491615800126754258944"
def inputClause3857 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,true),(57,false)]
theorem inputList3857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3857 (by decide) v hb
mask_input "3857|144687073708736512|5316911983139663491651257038140342272"
def inputClause3858 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,true),(57,false)]
theorem inputList3858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3858 (by decide) v hb
mask_input "3858|144687071561252864|5316911983139663491651257040287825920"
def inputClause3859 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,true),(57,false)]
theorem inputList3859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3859 (by decide) v hb
mask_input "3859|144686936269783040|5316911983139663491651257175579295744"
def inputClause3861 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(55,true),(57,false)]
theorem inputList3861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3861 (by decide) v hb
mask_input "3861|144678277615714304|5316911983139663491651265834233364480"
def inputClause3862 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,true),(57,false)]
theorem inputList3862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3862 (by decide) v hb
mask_input "3862|144678275468230656|5316911983139663491651265836380848128"
def inputClause3863 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,true),(57,false)]
theorem inputList3863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3863 (by decide) v hb
mask_input "3863|144678140176760832|5316911983139663491651265971672317952"
def inputClause3864 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,false),(55,true),(57,false)]
theorem inputList3864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3864 (by decide) v hb
mask_input "3864|144678138029277184|5316911983139663491651265973819801600"
def inputClause3865 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,true),(57,false)]
theorem inputList3865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3865 (by decide) v hb
mask_input "3865|144124123755315200|5316911983139663491651819988093763584"
def inputClause3866 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,true),(57,false)]
theorem inputList3866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3866 (by decide) v hb
mask_input "3866|144124121607831552|5316911983139663491651819990241247232"
def inputClause3867 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,true),(55,true),(57,false)]
theorem inputList3867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3867 (by decide) v hb
mask_input "3867|144123986316361728|5316911983139663491651820125532717056"
def inputClause3868 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,true),(55,true),(57,false)]
theorem inputList3868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3868 (by decide) v hb
mask_input "3868|144123984168878080|5316911983139663491651820127680200704"
def inputClause3869 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,true),(55,true),(57,false)]
theorem inputList3869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3869 (by decide) v hb
mask_input "3869|144115327662292992|5316911983139663491651828784186785792"
def inputClause3870 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,true),(55,true),(57,false)]
theorem inputList3870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3870 (by decide) v hb
mask_input "3870|144115325514809344|5316911983139663491651828786334269440"
def inputClause3872 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,true),(57,false)]
theorem inputList3872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3872 (by decide) v hb
mask_input "3872|5316911983139663491759343429197234176|36600682651844608"
def inputClause3873 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,false),(57,true)]
theorem inputList3873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3873 (by decide) v hb
mask_input "3873|36600682651844608|5316911983139663491759343429197234176"
def inputClause3874 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,false),(57,true)]
theorem inputList3874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3874 (by decide) v hb
mask_input "3874|36600680504360960|5316911983139663491759343431344717824"
end Percolation.MaskChain
