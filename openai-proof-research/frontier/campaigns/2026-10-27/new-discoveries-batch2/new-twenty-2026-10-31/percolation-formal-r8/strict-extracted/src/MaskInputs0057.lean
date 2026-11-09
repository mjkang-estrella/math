import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3032 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,false),(53,true),(58,false)]
theorem inputList3032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3032 (by decide) v hb
mask_input "3032|288300744895889408|649037107316853462591275280629760"
def inputClause3033 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,true),(58,false)]
theorem inputList3033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3033 (by decide) v hb
mask_input "3033|288248140136448000|649037107316853462643880040071168"
def inputClause3034 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,true),(58,false)]
theorem inputList3034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3034 (by decide) v hb
mask_input "3034|288248105776709632|649037107316853462643914399809536"
def inputClause3035 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,true),(58,false)]
theorem inputList3035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3035 (by decide) v hb
mask_input "3035|288248002697494528|649037107316853462644017479024640"
def inputClause3036 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,true),(53,true),(58,false)]
theorem inputList3036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3036 (by decide) v hb
mask_input "3036|288247968337756160|649037107316853462644051838763008"
def inputClause3037 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,true),(58,false)]
theorem inputList3037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3037 (by decide) v hb
mask_input "3037|288230547950403584|649037107316853462661472226115584"
def inputClause3038 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,true),(53,true),(58,false)]
theorem inputList3038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3038 (by decide) v hb
mask_input "3038|288230513590665216|649037107316853462661506585853952"
def inputClause3039 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,true),(53,true),(58,false)]
theorem inputList3039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3039 (by decide) v hb
mask_input "3039|288230410511450112|649037107316853462661609665069056"
def inputClause3040 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,true),(53,true),(58,false)]
theorem inputList3040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3040 (by decide) v hb
mask_input "3040|649037107316853741796688192864256|9095331983654912"
def inputClause3041 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,false),(58,true)]
theorem inputList3041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3041 (by decide) v hb
mask_input "3041|9095331983654912|649037107316853741796688192864256"
def inputClause3042 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,false),(58,true)]
theorem inputList3042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3042 (by decide) v hb
mask_input "3042|9095297623916544|649037107316853741796722552602624"
def inputClause3043 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,false),(58,true)]
theorem inputList3043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3043 (by decide) v hb
mask_input "3043|9095194544701440|649037107316853741796825631817728"
def inputClause3044 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,false),(58,true)]
theorem inputList3044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3044 (by decide) v hb
mask_input "3044|9095160184963072|649037107316853741796859991556096"
def inputClause3045 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,false),(58,true)]
theorem inputList3045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3045 (by decide) v hb
mask_input "3045|9077739797610496|649037107316853741814280378908672"
def inputClause3046 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,false),(58,true)]
theorem inputList3046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3046 (by decide) v hb
mask_input "3046|9077705437872128|649037107316853741814314738647040"
def inputClause3047 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,false),(58,true)]
theorem inputList3047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3047 (by decide) v hb
mask_input "3047|9077602358657024|649037107316853741814417817862144"
def inputClause3048 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,false),(53,false),(58,true)]
theorem inputList3048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3048 (by decide) v hb
mask_input "3048|9077567998918656|649037107316853741814452177600512"
def inputClause3049 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,false),(58,true)]
theorem inputList3049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3049 (by decide) v hb
mask_input "3049|9024963239477248|649037107316853741867056937041920"
def inputClause3050 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,false),(58,true)]
theorem inputList3050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3050 (by decide) v hb
mask_input "3050|9024928879738880|649037107316853741867091296780288"
def inputClause3051 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,false),(58,true)]
theorem inputList3051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3051 (by decide) v hb
mask_input "3051|9024825800523776|649037107316853741867194375995392"
def inputClause3052 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,true),(53,false),(58,true)]
theorem inputList3052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3052 (by decide) v hb
mask_input "3052|9024791440785408|649037107316853741867228735733760"
def inputClause3053 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,false),(58,true)]
theorem inputList3053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3053 (by decide) v hb
mask_input "3053|9007371053432832|649037107316853741884649123086336"
def inputClause3054 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,true),(53,false),(58,true)]
theorem inputList3054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3054 (by decide) v hb
mask_input "3054|9007336693694464|649037107316853741884683482824704"
def inputClause3055 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,true),(53,false),(58,true)]
theorem inputList3055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3055 (by decide) v hb
mask_input "3055|9007233614479360|649037107316853741884786562039808"
def inputClause3057 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,true),(58,true)]
theorem inputList3057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3057 (by decide) v hb
mask_input "3057|88132728913920|649037107316853750803887447605248"
def inputClause3058 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,true),(58,true)]
theorem inputList3058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3058 (by decide) v hb
mask_input "3058|88098369175552|649037107316853750803921807343616"
def inputClause3059 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,true),(58,true)]
theorem inputList3059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3059 (by decide) v hb
mask_input "3059|87995289960448|649037107316853750804024886558720"
def inputClause3060 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,true),(58,true)]
theorem inputList3060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3060 (by decide) v hb
mask_input "3060|87960930222080|649037107316853750804059246297088"
def inputClause3061 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,true),(58,true)]
theorem inputList3061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3061 (by decide) v hb
mask_input "3061|70540542869504|649037107316853750821479633649664"
def inputClause3062 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,true),(58,true)]
theorem inputList3062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3062 (by decide) v hb
mask_input "3062|70506183131136|649037107316853750821513993388032"
def inputClause3063 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,true),(58,true)]
theorem inputList3063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3063 (by decide) v hb
mask_input "3063|70403103916032|649037107316853750821617072603136"
def inputClause3065 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,true),(58,true)]
theorem inputList3065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3065 (by decide) v hb
mask_input "3065|17763984736256|649037107316853750874256191782912"
def inputClause3066 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,true),(58,true)]
theorem inputList3066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3066 (by decide) v hb
mask_input "3066|17729624997888|649037107316853750874290551521280"
def inputClause3067 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,true),(58,true)]
theorem inputList3067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3067 (by decide) v hb
mask_input "3067|17626545782784|649037107316853750874393630736384"
def inputClause3069 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,true),(58,true)]
theorem inputList3069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3069 (by decide) v hb
mask_input "3069|171798691840|649037107316853750891848377827328"
def inputClause3072 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,true),(53,true),(58,true)]
theorem inputList3072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3072 (by decide) v hb
mask_input "3072|649037107316853453566312041152512|297325708135366656"
def inputClause3073 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,false),(57,false)]
theorem inputList3073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3073 (by decide) v hb
mask_input "3073|148724899165241344|1298074214633706907132624082305024"
def inputClause3074 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,false),(57,false)]
theorem inputList3074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3074 (by decide) v hb
mask_input "3074|148724890575306752|1298074214633706907132632672239616"
def inputClause3075 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,false),(57,false)]
theorem inputList3075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3075 (by decide) v hb
mask_input "3075|148724349409427456|1298074214633706907133173838118912"
def inputClause3076 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,false),(57,false)]
theorem inputList3076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) inputClause3076 (by decide) v hb
mask_input "3076|148724340819492864|1298074214633706907133182428053504"
end Percolation.MaskChain
