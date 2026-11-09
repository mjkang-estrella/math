import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3077 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,false),(57,false)]
theorem inputList3077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3077 (by decide) v hb
mask_input "3077|148689714793152512|1298074214633706907167808454393856"
def inputClause3078 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,false),(57,false)]
theorem inputList3078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3078 (by decide) v hb
mask_input "3078|148689706203217920|1298074214633706907167817044328448"
def inputClause3079 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,false),(57,false)]
theorem inputList3079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3079 (by decide) v hb
mask_input "3079|148689165037338624|1298074214633706907168358210207744"
def inputClause3080 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,false),(52,false),(57,false)]
theorem inputList3080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3080 (by decide) v hb
mask_input "3080|148689156447404032|1298074214633706907168366800142336"
def inputClause3081 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,false),(57,false)]
theorem inputList3081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3081 (by decide) v hb
mask_input "3081|148654530421063680|1298074214633706907202992826482688"
def inputClause3082 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,false),(57,false)]
theorem inputList3082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3082 (by decide) v hb
mask_input "3082|148654521831129088|1298074214633706907203001416417280"
def inputClause3083 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,false),(57,false)]
theorem inputList3083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3083 (by decide) v hb
mask_input "3083|148653980665249792|1298074214633706907203542582296576"
def inputClause3084 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,true),(52,false),(57,false)]
theorem inputList3084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3084 (by decide) v hb
mask_input "3084|148653972075315200|1298074214633706907203551172231168"
def inputClause3085 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,false),(57,false)]
theorem inputList3085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3085 (by decide) v hb
mask_input "3085|148619346048974848|1298074214633706907238177198571520"
def inputClause3086 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,true),(52,false),(57,false)]
theorem inputList3086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3086 (by decide) v hb
mask_input "3086|148619337459040256|1298074214633706907238185788506112"
def inputClause3087 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,true),(52,false),(57,false)]
theorem inputList3087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3087 (by decide) v hb
mask_input "3087|148618796293160960|1298074214633706907238726954385408"
def inputClause3088 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,true),(52,false),(57,false)]
theorem inputList3088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3088 (by decide) v hb
mask_input "3088|148618787703226368|1298074214633706907238735544320000"
def inputClause3089 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,true),(57,false)]
theorem inputList3089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3089 (by decide) v hb
mask_input "3089|144221299537870848|1298074214633706911636223709675520"
def inputClause3090 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,true),(57,false)]
theorem inputList3090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3090 (by decide) v hb
mask_input "3090|144221290947936256|1298074214633706911636232299610112"
def inputClause3091 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,true),(57,false)]
theorem inputList3091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3091 (by decide) v hb
mask_input "3091|144220749782056960|1298074214633706911636773465489408"
def inputClause3092 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,true),(57,false)]
theorem inputList3092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3092 (by decide) v hb
mask_input "3092|144220741192122368|1298074214633706911636782055424000"
def inputClause3093 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,true),(57,false)]
theorem inputList3093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3093 (by decide) v hb
mask_input "3093|144186115165782016|1298074214633706911671408081764352"
def inputClause3094 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,true),(57,false)]
theorem inputList3094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3094 (by decide) v hb
mask_input "3094|144186106575847424|1298074214633706911671416671698944"
def inputClause3095 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,true),(57,false)]
theorem inputList3095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3095 (by decide) v hb
mask_input "3095|144185565409968128|1298074214633706911671957837578240"
def inputClause3096 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,false),(52,true),(57,false)]
theorem inputList3096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3096 (by decide) v hb
mask_input "3096|144185556820033536|1298074214633706911671966427512832"
def inputClause3097 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,true),(57,false)]
theorem inputList3097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3097 (by decide) v hb
mask_input "3097|144150930793693184|1298074214633706911706592453853184"
def inputClause3098 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,true),(57,false)]
theorem inputList3098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3098 (by decide) v hb
mask_input "3098|144150922203758592|1298074214633706911706601043787776"
def inputClause3099 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,true),(57,false)]
theorem inputList3099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3099 (by decide) v hb
mask_input "3099|144150381037879296|1298074214633706911707142209667072"
def inputClause3100 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,true),(52,true),(57,false)]
theorem inputList3100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3100 (by decide) v hb
mask_input "3100|144150372447944704|1298074214633706911707150799601664"
def inputClause3101 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,true),(57,false)]
theorem inputList3101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3101 (by decide) v hb
mask_input "3101|144115746421604352|1298074214633706911741776825942016"
def inputClause3102 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,true),(52,true),(57,false)]
theorem inputList3102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3102 (by decide) v hb
mask_input "3102|144115737831669760|1298074214633706911741785415876608"
def inputClause3103 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,true),(52,true),(57,false)]
theorem inputList3103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3103 (by decide) v hb
mask_input "3103|144115196665790464|1298074214633706911742326581755904"
def inputClause3105 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,false),(57,true)]
theorem inputList3105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3105 (by decide) v hb
mask_input "3105|4609711089385472|1298074214633707051247812158160896"
def inputClause3106 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,false),(57,true)]
theorem inputList3106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3106 (by decide) v hb
mask_input "3106|4609702499450880|1298074214633707051247820748095488"
def inputClause3107 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,false),(57,true)]
theorem inputList3107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3107 (by decide) v hb
mask_input "3107|4609161333571584|1298074214633707051248361913974784"
def inputClause3108 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,false),(57,true)]
theorem inputList3108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3108 (by decide) v hb
mask_input "3108|4609152743636992|1298074214633707051248370503909376"
def inputClause3109 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,false),(57,true)]
theorem inputList3109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3109 (by decide) v hb
mask_input "3109|4574526717296640|1298074214633707051282996530249728"
def inputClause3110 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,false),(57,true)]
theorem inputList3110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3110 (by decide) v hb
mask_input "3110|4574518127362048|1298074214633707051283005120184320"
def inputClause3111 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,false),(57,true)]
theorem inputList3111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3111 (by decide) v hb
mask_input "3111|4573976961482752|1298074214633707051283546286063616"
def inputClause3112 : CNF.NClause := [(110,true),(33,true),(39,true),(45,true),(46,false),(52,false),(57,true)]
theorem inputList3112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3112 (by decide) v hb
mask_input "3112|4573968371548160|1298074214633707051283554875998208"
def inputClause3113 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,false),(57,true)]
theorem inputList3113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3113 (by decide) v hb
mask_input "3113|4539342345207808|1298074214633707051318180902338560"
def inputClause3114 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,false),(57,true)]
theorem inputList3114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3114 (by decide) v hb
mask_input "3114|4539333755273216|1298074214633707051318189492273152"
def inputClause3115 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,false),(57,true)]
theorem inputList3115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3115 (by decide) v hb
mask_input "3115|4538792589393920|1298074214633707051318730658152448"
def inputClause3116 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,true),(52,false),(57,true)]
theorem inputList3116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3116 (by decide) v hb
mask_input "3116|4538783999459328|1298074214633707051318739248087040"
def inputClause3117 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,false),(57,true)]
theorem inputList3117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3117 (by decide) v hb
mask_input "3117|4504157973118976|1298074214633707051353365274427392"
end Percolation.MaskChain
