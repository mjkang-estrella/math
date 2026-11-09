import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3159 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,true),(60,false)]
theorem inputList3159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3159 (by decide) v hb
mask_input "3159|1152991890530893824|2596148429267413850298718107992064"
def inputClause3160 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,true),(60,false)]
theorem inputList3160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3160 (by decide) v hb
mask_input "3160|1152991873351024640|2596148429267413850298735287861248"
def inputClause3161 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,true),(60,false)]
theorem inputList3161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3161 (by decide) v hb
mask_input "3161|1152926194711134208|2596148429267413850364413927751680"
def inputClause3162 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,true),(60,false)]
theorem inputList3162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3162 (by decide) v hb
mask_input "3162|1152926177531265024|2596148429267413850364431107620864"
def inputClause3163 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,true),(60,false)]
theorem inputList3163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3163 (by decide) v hb
mask_input "3163|1152925919833227264|2596148429267413850364688805658624"
def inputClause3164 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,true),(60,false)]
theorem inputList3164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3164 (by decide) v hb
mask_input "3164|1152925902653358080|2596148429267413850364705985527808"
def inputClause3165 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,true),(60,false)]
theorem inputList3165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3165 (by decide) v hb
mask_input "3165|1152921796664623104|2596148429267413850368811974262784"
def inputClause3166 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,true),(55,true),(60,false)]
theorem inputList3166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3166 (by decide) v hb
mask_input "3166|1152921779484753920|2596148429267413850368829154131968"
def inputClause3167 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,true),(60,false)]
theorem inputList3167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3167 (by decide) v hb
mask_input "3167|1152921521786716160|2596148429267413850369086852169728"
def inputClause3169 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,false),(60,true)]
theorem inputList3169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3169 (by decide) v hb
mask_input "3169|36103855867428864|2596148429267414967186752771457024"
def inputClause3170 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,false),(60,true)]
theorem inputList3170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3170 (by decide) v hb
mask_input "3170|36103838687559680|2596148429267414967186769951326208"
def inputClause3171 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,false),(60,true)]
theorem inputList3171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3171 (by decide) v hb
mask_input "3171|36103580989521920|2596148429267414967187027649363968"
def inputClause3172 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,false),(60,true)]
theorem inputList3172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3172 (by decide) v hb
mask_input "3172|36103563809652736|2596148429267414967187044829233152"
def inputClause3173 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,false),(60,true)]
theorem inputList3173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3173 (by decide) v hb
mask_input "3173|36099457820917760|2596148429267414967191150817968128"
def inputClause3174 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,false),(60,true)]
theorem inputList3174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3174 (by decide) v hb
mask_input "3174|36099440641048576|2596148429267414967191167997837312"
def inputClause3175 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,false),(60,true)]
theorem inputList3175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3175 (by decide) v hb
mask_input "3175|36099182943010816|2596148429267414967191425695875072"
def inputClause3176 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,false),(60,true)]
theorem inputList3176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3176 (by decide) v hb
mask_input "3176|36099165763141632|2596148429267414967191442875744256"
def inputClause3177 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,false),(60,true)]
theorem inputList3177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3177 (by decide) v hb
mask_input "3177|36033487123251200|2596148429267414967257121515634688"
def inputClause3178 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,false),(60,true)]
theorem inputList3178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3178 (by decide) v hb
mask_input "3178|36033469943382016|2596148429267414967257138695503872"
def inputClause3179 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,false),(60,true)]
theorem inputList3179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3179 (by decide) v hb
mask_input "3179|36033212245344256|2596148429267414967257396393541632"
def inputClause3180 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,false),(60,true)]
theorem inputList3180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3180 (by decide) v hb
mask_input "3180|36033195065475072|2596148429267414967257413573410816"
def inputClause3181 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,false),(60,true)]
theorem inputList3181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3181 (by decide) v hb
mask_input "3181|36029089076740096|2596148429267414967261519562145792"
def inputClause3182 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,true),(55,false),(60,true)]
theorem inputList3182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3182 (by decide) v hb
mask_input "3182|36029071896870912|2596148429267414967261536742014976"
def inputClause3183 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,false),(60,true)]
theorem inputList3183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3183 (by decide) v hb
mask_input "3183|36028814198833152|2596148429267414967261794440052736"
def inputClause3185 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,true),(60,true)]
theorem inputList3185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3185 (by decide) v hb
mask_input "3185|75058848464896|2596148429267415003215549790420992"
def inputClause3186 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,false),(55,true),(60,true)]
theorem inputList3186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3186 (by decide) v hb
mask_input "3186|75041668595712|2596148429267415003215566970290176"
def inputClause3187 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,true),(60,true)]
theorem inputList3187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3187 (by decide) v hb
mask_input "3187|74783970557952|2596148429267415003215824668327936"
def inputClause3188 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,true),(60,true)]
theorem inputList3188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3188 (by decide) v hb
mask_input "3188|74766790688768|2596148429267415003215841848197120"
def inputClause3189 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,false),(55,true),(60,true)]
theorem inputList3189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3189 (by decide) v hb
mask_input "3189|70660801953792|2596148429267415003219947836932096"
def inputClause3190 : CNF.NClause := [(111,true),(34,true),(38,false),(42,true),(46,false),(55,true),(60,true)]
theorem inputList3190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3190 (by decide) v hb
mask_input "3190|70643622084608|2596148429267415003219965016801280"
def inputClause3191 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,true),(60,true)]
theorem inputList3191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3191 (by decide) v hb
mask_input "3191|70385924046848|2596148429267415003220222714839040"
def inputClause3193 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,true),(55,true),(60,true)]
theorem inputList3193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3193 (by decide) v hb
mask_input "3193|4690104287232|2596148429267415003285918534598656"
def inputClause3194 : CNF.NClause := [(111,true),(34,true),(38,false),(42,false),(46,true),(55,true),(60,true)]
theorem inputList3194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3194 (by decide) v hb
mask_input "3194|4672924418048|2596148429267415003285935714467840"
def inputClause3195 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,true),(55,true),(60,true)]
theorem inputList3195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3195 (by decide) v hb
mask_input "3195|4415226380288|2596148429267415003286193412505600"
def inputClause3197 : CNF.NClause := [(111,true),(34,false),(38,false),(42,true),(46,true),(55,true),(60,true)]
theorem inputList3197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3197 (by decide) v hb
mask_input "3197|292057776128|2596148429267415003290316581109760"
def inputClause3199 : CNF.NClause := [(111,false),(34,false),(38,true),(42,true),(46,true),(55,true),(60,true)]
theorem inputList3199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3199 (by decide) v hb
mask_input "3199|2596148429267413814265265344479232|1189025343294406656"
def inputClause3200 : CNF.NClause := [(111,false),(34,true),(38,true),(42,true),(46,true),(55,true),(60,true)]
theorem inputList3200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) inputClause3200 (by decide) v hb
mask_input "3200|2596148429267413814265248164610048|1189025360474275840"
def inputClause3201 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(46,false),(54,false),(59,false)]
theorem inputList3201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3201 (by decide) v hb
mask_input "3201|594555419456700416|5192296858534827628530496329220096"
def inputClause3202 : CNF.NClause := [(112,true),(32,true),(40,false),(43,false),(46,false),(54,false),(59,false)]
theorem inputList3202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3202 (by decide) v hb
mask_input "3202|594555415161733120|5192296858534827628530500624187392"
def inputClause3203 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,false),(59,false)]
theorem inputList3203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 19) 19) (activationX_mem 19) inputClause3203 (by decide) v hb
mask_input "3203|594554319945072640|5192296858534827628531595840847872"
end Percolation.MaskChain
