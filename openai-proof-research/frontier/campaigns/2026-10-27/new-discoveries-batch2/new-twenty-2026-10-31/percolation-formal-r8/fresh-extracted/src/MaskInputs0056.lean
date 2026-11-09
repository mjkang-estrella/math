import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2992 : CNF.NClause := [(108,false),(46,true),(47,true),(48,true),(49,true),(50,false),(61,true)]
theorem inputList2992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2992 (by decide) v hb
mask_input "2992|324518553658426727909055927418880|2306898540376358912"
def inputClause2993 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,true),(61,true)]
theorem inputList2993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2993 (by decide) v hb
mask_input "2993|1055531162664960|324518553658429033752065141112832"
def inputClause2994 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,true),(61,true)]
theorem inputList2994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2994 (by decide) v hb
mask_input "2994|985162418487296|324518553658429033822433885290496"
def inputClause2995 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,true),(61,true)]
theorem inputList2995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2995 (by decide) v hb
mask_input "2995|914793674309632|324518553658429033892802629468160"
def inputClause2996 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,true),(61,true)]
theorem inputList2996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2996 (by decide) v hb
mask_input "2996|844424930131968|324518553658429033963171373645824"
def inputClause2997 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,false),(50,true),(61,true)]
theorem inputList2997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2997 (by decide) v hb
mask_input "2997|774056185954304|324518553658429034033540117823488"
def inputClause2998 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,true),(61,true)]
theorem inputList2998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2998 (by decide) v hb
mask_input "2998|703687441776640|324518553658429034103908862001152"
def inputClause2999 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,true),(61,true)]
theorem inputList2999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2999 (by decide) v hb
mask_input "2999|633318697598976|324518553658429034174277606178816"
def inputClause3000 : CNF.NClause := [(108,false),(46,true),(47,true),(48,true),(49,false),(50,true),(61,true)]
theorem inputList3000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3000 (by decide) v hb
mask_input "3000|324518553658426727346105973997568|2307461490329780224"
def inputClause3001 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,true),(61,true)]
theorem inputList3001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3001 (by decide) v hb
mask_input "3001|492581209243648|324518553658429034315015094534144"
def inputClause3002 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,true),(61,true)]
theorem inputList3002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3002 (by decide) v hb
mask_input "3002|422212465065984|324518553658429034385383838711808"
def inputClause3003 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,true),(61,true)]
theorem inputList3003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3003 (by decide) v hb
mask_input "3003|351843720888320|324518553658429034455752582889472"
def inputClause3004 : CNF.NClause := [(108,false),(46,true),(47,true),(48,false),(49,true),(50,true),(61,true)]
theorem inputList3004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3004 (by decide) v hb
mask_input "3004|324518553658426727064630997286912|2307742965306490880"
def inputClause3005 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,true),(61,true)]
theorem inputList3005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3005 (by decide) v hb
mask_input "3005|211106232532992|324518553658429034596490071244800"
def inputClause3006 : CNF.NClause := [(108,false),(46,true),(47,false),(48,true),(49,true),(50,true),(61,true)]
theorem inputList3006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3006 (by decide) v hb
mask_input "3006|324518553658426726923893508931584|2307883702794846208"
def inputClause3007 : CNF.NClause := [(108,false),(46,false),(47,true),(48,true),(49,true),(50,true),(61,true)]
theorem inputList3007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3007 (by decide) v hb
mask_input "3007|324518553658426726853524764753920|2307954071539023872"
def inputClause3008 : CNF.NClause := [(108,false),(46,true),(47,true),(48,true),(49,true),(50,true),(61,true)]
theorem inputList3008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause3008 (by decide) v hb
mask_input "3008|324518553658426726783156020576256|2308024440283201536"
def inputClause3009 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,false),(58,false)]
theorem inputList3009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3009 (by decide) v hb
mask_input "3009|297325708135366656|649037107316853453566312041152512"
def inputClause3010 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,false),(58,false)]
theorem inputList3010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3010 (by decide) v hb
mask_input "3010|297325673775628288|649037107316853453566346400890880"
def inputClause3011 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,false),(58,false)]
theorem inputList3011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3011 (by decide) v hb
mask_input "3011|297325570696413184|649037107316853453566449480105984"
def inputClause3012 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,false),(58,false)]
theorem inputList3012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3012 (by decide) v hb
mask_input "3012|297325536336674816|649037107316853453566483839844352"
def inputClause3013 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,false),(58,false)]
theorem inputList3013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3013 (by decide) v hb
mask_input "3013|297308115949322240|649037107316853453583904227196928"
def inputClause3014 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,false),(58,false)]
theorem inputList3014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3014 (by decide) v hb
mask_input "3014|297308081589583872|649037107316853453583938586935296"
def inputClause3015 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,false),(58,false)]
theorem inputList3015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3015 (by decide) v hb
mask_input "3015|297307978510368768|649037107316853453584041666150400"
def inputClause3016 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,false),(53,false),(58,false)]
theorem inputList3016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3016 (by decide) v hb
mask_input "3016|297307944150630400|649037107316853453584076025888768"
def inputClause3017 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,false),(58,false)]
theorem inputList3017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3017 (by decide) v hb
mask_input "3017|297255339391188992|649037107316853453636680785330176"
def inputClause3018 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,false),(58,false)]
theorem inputList3018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3018 (by decide) v hb
mask_input "3018|297255305031450624|649037107316853453636715145068544"
def inputClause3019 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,false),(58,false)]
theorem inputList3019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3019 (by decide) v hb
mask_input "3019|297255201952235520|649037107316853453636818224283648"
def inputClause3020 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,true),(53,false),(58,false)]
theorem inputList3020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3020 (by decide) v hb
mask_input "3020|297255167592497152|649037107316853453636852584022016"
def inputClause3021 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,false),(58,false)]
theorem inputList3021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3021 (by decide) v hb
mask_input "3021|297237747205144576|649037107316853453654272971374592"
def inputClause3022 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,true),(53,false),(58,false)]
theorem inputList3022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3022 (by decide) v hb
mask_input "3022|297237712845406208|649037107316853453654307331112960"
def inputClause3023 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,true),(53,false),(58,false)]
theorem inputList3023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3023 (by decide) v hb
mask_input "3023|297237609766191104|649037107316853453654410410328064"
def inputClause3024 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,true),(53,false),(58,false)]
theorem inputList3024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3024 (by decide) v hb
mask_input "3024|297237575406452736|649037107316853453654444770066432"
def inputClause3025 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,true),(58,false)]
theorem inputList3025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3025 (by decide) v hb
mask_input "3025|288318508880625664|649037107316853462573511295893504"
def inputClause3026 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,true),(58,false)]
theorem inputList3026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3026 (by decide) v hb
mask_input "3026|288318474520887296|649037107316853462573545655631872"
def inputClause3027 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,true),(58,false)]
theorem inputList3027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3027 (by decide) v hb
mask_input "3027|288318371441672192|649037107316853462573648734846976"
def inputClause3028 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,true),(58,false)]
theorem inputList3028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3028 (by decide) v hb
mask_input "3028|288318337081933824|649037107316853462573683094585344"
def inputClause3029 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,true),(58,false)]
theorem inputList3029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3029 (by decide) v hb
mask_input "3029|288300916694581248|649037107316853462591103481937920"
def inputClause3030 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,true),(58,false)]
theorem inputList3030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3030 (by decide) v hb
mask_input "3030|288300882334842880|649037107316853462591137841676288"
def inputClause3031 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,true),(58,false)]
theorem inputList3031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) inputClause3031 (by decide) v hb
mask_input "3031|288300779255627776|649037107316853462591240920891392"
end Percolation.MaskChain
