import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause790 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,true),(29,false)]
theorem inputList790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause790 (by decide) v hb
mask_input "790|537395264|18889465931478589244420"
def inputClause791 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,true),(29,false)]
theorem inputList791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause791 (by decide) v hb
mask_input "791|537395204|18889465931478589244480"
def inputClause792 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,true),(29,false)]
theorem inputList792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause792 (by decide) v hb
mask_input "792|537395200|18889465931478589244484"
def inputClause793 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,true),(29,false)]
theorem inputList793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause793 (by decide) v hb
mask_input "793|536872004|18889465931478589767680"
def inputClause794 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,true),(29,false)]
theorem inputList794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause794 (by decide) v hb
mask_input "794|536872000|18889465931478589767684"
def inputClause795 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,true),(29,false)]
theorem inputList795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause795 (by decide) v hb
mask_input "795|536871940|18889465931478589767744"
def inputClause796 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,true),(23,true),(29,false)]
theorem inputList796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause796 (by decide) v hb
mask_input "796|536871936|18889465931478589767748"
def inputClause797 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,true),(29,false)]
theorem inputList797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause797 (by decide) v hb
mask_input "797|536870980|18889465931478589768704"
def inputClause798 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,true),(29,false)]
theorem inputList798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause798 (by decide) v hb
mask_input "798|536870976|18889465931478589768708"
def inputClause799 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,true),(29,false)]
theorem inputList799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause799 (by decide) v hb
mask_input "799|536870916|18889465931478589768768"
def inputClause801 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,false),(29,true)]
theorem inputList801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause801 (by decide) v hb
mask_input "801|8913988|18889465931479117725696"
def inputClause802 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,false),(29,true)]
theorem inputList802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause802 (by decide) v hb
mask_input "802|8913984|18889465931479117725700"
def inputClause803 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,false),(29,true)]
theorem inputList803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause803 (by decide) v hb
mask_input "803|8913924|18889465931479117725760"
def inputClause804 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,false),(29,true)]
theorem inputList804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause804 (by decide) v hb
mask_input "804|8913920|18889465931479117725764"
def inputClause805 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,false),(29,true)]
theorem inputList805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause805 (by decide) v hb
mask_input "805|8912964|18889465931479117726720"
def inputClause806 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,false),(29,true)]
theorem inputList806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause806 (by decide) v hb
mask_input "806|8912960|18889465931479117726724"
def inputClause807 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,false),(29,true)]
theorem inputList807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause807 (by decide) v hb
mask_input "807|8912900|18889465931479117726784"
def inputClause808 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,false),(29,true)]
theorem inputList808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause808 (by decide) v hb
mask_input "808|8912896|18889465931479117726788"
def inputClause809 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,false),(29,true)]
theorem inputList809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause809 (by decide) v hb
mask_input "809|8389700|18889465931479118249984"
def inputClause810 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,false),(29,true)]
theorem inputList810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause810 (by decide) v hb
mask_input "810|8389696|18889465931479118249988"
def inputClause811 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,false),(29,true)]
theorem inputList811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause811 (by decide) v hb
mask_input "811|8389636|18889465931479118250048"
def inputClause812 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,true),(23,false),(29,true)]
theorem inputList812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause812 (by decide) v hb
mask_input "812|8389632|18889465931479118250052"
def inputClause813 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,false),(29,true)]
theorem inputList813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause813 (by decide) v hb
mask_input "813|8388676|18889465931479118251008"
def inputClause814 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,false),(29,true)]
theorem inputList814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause814 (by decide) v hb
mask_input "814|8388672|18889465931479118251012"
def inputClause815 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,false),(29,true)]
theorem inputList815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause815 (by decide) v hb
mask_input "815|8388612|18889465931479118251072"
def inputClause817 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,true),(29,true)]
theorem inputList817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause817 (by decide) v hb
mask_input "817|525380|18889465931479126114304"
def inputClause818 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,true),(29,true)]
theorem inputList818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause818 (by decide) v hb
mask_input "818|525376|18889465931479126114308"
def inputClause819 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,true),(29,true)]
theorem inputList819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause819 (by decide) v hb
mask_input "819|525316|18889465931479126114368"
def inputClause820 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,true),(29,true)]
theorem inputList820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause820 (by decide) v hb
mask_input "820|525312|18889465931479126114372"
def inputClause821 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,true),(29,true)]
theorem inputList821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause821 (by decide) v hb
mask_input "821|524356|18889465931479126115328"
def inputClause822 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,true),(29,true)]
theorem inputList822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause822 (by decide) v hb
mask_input "822|524352|18889465931479126115332"
def inputClause823 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,true),(29,true)]
theorem inputList823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause823 (by decide) v hb
mask_input "823|524292|18889465931479126115392"
def inputClause824 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,false),(23,true),(29,true)]
theorem inputList824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause824 (by decide) v hb
mask_input "824|18889465931478581379072|545260612"
def inputClause825 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,true),(29,true)]
theorem inputList825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause825 (by decide) v hb
mask_input "825|1092|18889465931479126638592"
def inputClause826 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,true),(29,true)]
theorem inputList826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause826 (by decide) v hb
mask_input "826|1088|18889465931479126638596"
def inputClause827 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,true),(29,true)]
theorem inputList827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause827 (by decide) v hb
mask_input "827|1028|18889465931479126638656"
def inputClause829 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,true),(29,true)]
theorem inputList829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause829 (by decide) v hb
mask_input "829|68|18889465931479126639616"
def inputClause832 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,true),(29,true)]
theorem inputList832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause832 (by decide) v hb
mask_input "832|18889465931478580854784|545784900"
def inputClause833 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,false),(26,false)]
theorem inputList833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause833 (by decide) v hb
mask_input "833|71370248|37778931862957161709568"
def inputClause834 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,false),(26,false)]
theorem inputList834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause834 (by decide) v hb
mask_input "834|71370240|37778931862957161709576"
end Percolation.MaskChain
