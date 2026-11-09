import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3118 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,true),(52,false),(57,true)]
theorem inputList3118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3118 (by decide) v hb
mask_input "3118|4504149383184384|1298074214633707051353373864361984"
def inputClause3119 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,true),(52,false),(57,true)]
theorem inputList3119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3119 (by decide) v hb
mask_input "3119|4503608217305088|1298074214633707051353915030241280"
def inputClause3121 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,true),(57,true)]
theorem inputList3121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3121 (by decide) v hb
mask_input "3121|106111462014976|1298074214633707055751411785531392"
def inputClause3122 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,true),(57,true)]
theorem inputList3122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3122 (by decide) v hb
mask_input "3122|106102872080384|1298074214633707055751420375465984"
def inputClause3123 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,true),(57,true)]
theorem inputList3123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3123 (by decide) v hb
mask_input "3123|105561706201088|1298074214633707055751961541345280"
def inputClause3124 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,true),(57,true)]
theorem inputList3124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3124 (by decide) v hb
mask_input "3124|105553116266496|1298074214633707055751970131279872"
def inputClause3125 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,false),(52,true),(57,true)]
theorem inputList3125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3125 (by decide) v hb
mask_input "3125|70927089926144|1298074214633707055786596157620224"
def inputClause3126 : CNF.NClause := [(110,true),(33,true),(39,false),(45,true),(46,false),(52,true),(57,true)]
theorem inputList3126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3126 (by decide) v hb
mask_input "3126|70918499991552|1298074214633707055786604747554816"
def inputClause3127 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,true),(57,true)]
theorem inputList3127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3127 (by decide) v hb
mask_input "3127|70377334112256|1298074214633707055787145913434112"
def inputClause3128 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,false),(52,true),(57,true)]
theorem inputList3128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3128 (by decide) v hb
mask_input "3128|1298074214633706907202992826482688|148654530421063680"
def inputClause3129 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,true),(57,true)]
theorem inputList3129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3129 (by decide) v hb
mask_input "3129|35742717837312|1298074214633707055821780529709056"
def inputClause3130 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,true),(57,true)]
theorem inputList3130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3130 (by decide) v hb
mask_input "3130|35734127902720|1298074214633707055821789119643648"
def inputClause3131 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,true),(57,true)]
theorem inputList3131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3131 (by decide) v hb
mask_input "3131|35192962023424|1298074214633707055822330285522944"
def inputClause3132 : CNF.NClause := [(110,false),(33,true),(39,true),(45,false),(46,true),(52,true),(57,true)]
theorem inputList3132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3132 (by decide) v hb
mask_input "3132|1298074214633706907167808454393856|148689714793152512"
def inputClause3133 : CNF.NClause := [(110,true),(33,false),(39,false),(45,true),(46,true),(52,true),(57,true)]
theorem inputList3133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3133 (by decide) v hb
mask_input "3133|558345748480|1298074214633707055856964901797888"
def inputClause3134 : CNF.NClause := [(110,false),(33,true),(39,false),(45,true),(46,true),(52,true),(57,true)]
theorem inputList3134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3134 (by decide) v hb
mask_input "3134|1298074214633706907133173838118912|148724349409427456"
def inputClause3135 : CNF.NClause := [(110,false),(33,false),(39,true),(45,true),(46,true),(52,true),(57,true)]
theorem inputList3135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3135 (by decide) v hb
mask_input "3135|1298074214633706907132632672239616|148724890575306752"
def inputClause3136 : CNF.NClause := [(110,false),(33,true),(39,true),(45,true),(46,true),(52,true),(57,true)]
theorem inputList3136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3136 (by decide) v hb
mask_input "3136|1298074214633706907132624082305024|148724899165241344"
def inputClause3137 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,false),(60,false)]
theorem inputList3137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3137 (by decide) v hb
mask_input "3137|1189025360474275840|2596148429267413814265248164610048"
def inputClause3138 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,false),(60,false)]
theorem inputList3138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3138 (by decide) v hb
mask_input "3138|1189025343294406656|2596148429267413814265265344479232"
def inputClause3139 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,false),(60,false)]
theorem inputList3139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3139 (by decide) v hb
mask_input "3139|1189025085596368896|2596148429267413814265523042516992"
def inputClause3140 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,false),(60,false)]
theorem inputList3140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3140 (by decide) v hb
mask_input "3140|1189025068416499712|2596148429267413814265540222386176"
def inputClause3141 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,false),(60,false)]
theorem inputList3141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3141 (by decide) v hb
mask_input "3141|1189020962427764736|2596148429267413814269646211121152"
def inputClause3142 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,false),(60,false)]
theorem inputList3142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3142 (by decide) v hb
mask_input "3142|1189020945247895552|2596148429267413814269663390990336"
def inputClause3143 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,false),(60,false)]
theorem inputList3143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3143 (by decide) v hb
mask_input "3143|1189020687549857792|2596148429267413814269921089028096"
def inputClause3144 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,false),(60,false)]
theorem inputList3144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3144 (by decide) v hb
mask_input "3144|1189020670369988608|2596148429267413814269938268897280"
def inputClause3145 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,false),(60,false)]
theorem inputList3145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3145 (by decide) v hb
mask_input "3145|1188954991730098176|2596148429267413814335616908787712"
def inputClause3146 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,false),(60,false)]
theorem inputList3146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3146 (by decide) v hb
mask_input "3146|1188954974550228992|2596148429267413814335634088656896"
def inputClause3147 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,false),(60,false)]
theorem inputList3147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3147 (by decide) v hb
mask_input "3147|1188954716852191232|2596148429267413814335891786694656"
def inputClause3148 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,false),(60,false)]
theorem inputList3148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3148 (by decide) v hb
mask_input "3148|1188954699672322048|2596148429267413814335908966563840"
def inputClause3149 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,false),(60,false)]
theorem inputList3149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3149 (by decide) v hb
mask_input "3149|1188950593683587072|2596148429267413814340014955298816"
def inputClause3150 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,true),(55,false),(60,false)]
theorem inputList3150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3150 (by decide) v hb
mask_input "3150|1188950576503717888|2596148429267413814340032135168000"
def inputClause3151 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,false),(60,false)]
theorem inputList3151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3151 (by decide) v hb
mask_input "3151|1188950318805680128|2596148429267413814340289833205760"
def inputClause3152 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,true),(55,false),(60,false)]
theorem inputList3152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3152 (by decide) v hb
mask_input "3152|1188950301625810944|2596148429267413814340307013074944"
def inputClause3153 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,true),(60,false)]
theorem inputList3153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3153 (by decide) v hb
mask_input "3153|1152996563455311872|2596148429267413850294045183574016"
def inputClause3154 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,true),(60,false)]
theorem inputList3154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3154 (by decide) v hb
mask_input "3154|1152996546275442688|2596148429267413850294062363443200"
def inputClause3155 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,true),(60,false)]
theorem inputList3155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3155 (by decide) v hb
mask_input "3155|1152996288577404928|2596148429267413850294320061480960"
def inputClause3156 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,true),(60,false)]
theorem inputList3156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3156 (by decide) v hb
mask_input "3156|1152996271397535744|2596148429267413850294337241350144"
def inputClause3157 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,true),(60,false)]
theorem inputList3157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3157 (by decide) v hb
mask_input "3157|1152992165408800768|2596148429267413850298443230085120"
def inputClause3158 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,true),(60,false)]
theorem inputList3158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3158 (by decide) v hb
mask_input "3158|1152992148228931584|2596148429267413850298460409954304"
end Percolation.MaskChain
