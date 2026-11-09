import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2946 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,false),(61,false)]
theorem inputList2946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2946 (by decide) v hb
mask_input "2946|2307954071539023872|324518553658426726853524764753920"
def inputClause2947 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,false),(61,false)]
theorem inputList2947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2947 (by decide) v hb
mask_input "2947|2307883702794846208|324518553658426726923893508931584"
def inputClause2948 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,false),(61,false)]
theorem inputList2948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2948 (by decide) v hb
mask_input "2948|2307813334050668544|324518553658426726994262253109248"
def inputClause2950 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,false),(61,false)]
theorem inputList2950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2950 (by decide) v hb
mask_input "2950|2307672596562313216|324518553658426727134999741464576"
def inputClause2951 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,false),(61,false)]
theorem inputList2951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2951 (by decide) v hb
mask_input "2951|2307602227818135552|324518553658426727205368485642240"
def inputClause2952 : CNF.NClause := [(108,true),(46,true),(47,true),(48,true),(49,false),(50,false),(61,false)]
theorem inputList2952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2952 (by decide) v hb
mask_input "2952|2307531859073957888|324518553658426727275737229819904"
def inputClause2953 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,false),(61,false)]
theorem inputList2953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2953 (by decide) v hb
mask_input "2953|2307461490329780224|324518553658426727346105973997568"
def inputClause2954 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,false),(61,false)]
theorem inputList2954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2954 (by decide) v hb
mask_input "2954|2307391121585602560|324518553658426727416474718175232"
def inputClause2955 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,false),(61,false)]
theorem inputList2955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2955 (by decide) v hb
mask_input "2955|2307320752841424896|324518553658426727486843462352896"
def inputClause2957 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,false),(61,false)]
theorem inputList2957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2957 (by decide) v hb
mask_input "2957|2307180015353069568|324518553658426727627580950708224"
def inputClause2958 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,true),(50,false),(61,false)]
theorem inputList2958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2958 (by decide) v hb
mask_input "2958|2307109646608891904|324518553658426727697949694885888"
def inputClause2959 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,true),(50,false),(61,false)]
theorem inputList2959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2959 (by decide) v hb
mask_input "2959|2307039277864714240|324518553658426727768318439063552"
def inputClause2960 : CNF.NClause := [(108,true),(46,true),(47,true),(48,true),(49,true),(50,false),(61,false)]
theorem inputList2960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2960 (by decide) v hb
mask_input "2960|2306968909120536576|324518553658426727838687183241216"
def inputClause2961 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,true),(61,false)]
theorem inputList2961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2961 (by decide) v hb
mask_input "2961|2306898540376358912|324518553658426727909055927418880"
def inputClause2962 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,true),(61,false)]
theorem inputList2962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2962 (by decide) v hb
mask_input "2962|2306828171632181248|324518553658426727979424671596544"
def inputClause2963 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,true),(61,false)]
theorem inputList2963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2963 (by decide) v hb
mask_input "2963|2306757802888003584|324518553658426728049793415774208"
def inputClause2964 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,true),(61,false)]
theorem inputList2964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2964 (by decide) v hb
mask_input "2964|2306687434143825920|324518553658426728120162159951872"
def inputClause2966 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,true),(61,false)]
theorem inputList2966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2966 (by decide) v hb
mask_input "2966|2306546696655470592|324518553658426728260899648307200"
def inputClause2967 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,true),(61,false)]
theorem inputList2967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2967 (by decide) v hb
mask_input "2967|2306476327911292928|324518553658426728331268392484864"
def inputClause2969 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,true),(61,false)]
theorem inputList2969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2969 (by decide) v hb
mask_input "2969|2306335590422937600|324518553658426728472005880840192"
def inputClause2970 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,true),(61,false)]
theorem inputList2970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2970 (by decide) v hb
mask_input "2970|2306265221678759936|324518553658426728542374625017856"
def inputClause2971 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,true),(61,false)]
theorem inputList2971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2971 (by decide) v hb
mask_input "2971|2306194852934582272|324518553658426728612743369195520"
def inputClause2973 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,true),(61,false)]
theorem inputList2973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2973 (by decide) v hb
mask_input "2973|2306054115446226944|324518553658426728753480857550848"
def inputClause2974 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,true),(50,true),(61,false)]
theorem inputList2974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2974 (by decide) v hb
mask_input "2974|2305983746702049280|324518553658426728823849601728512"
def inputClause2975 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,true),(50,true),(61,false)]
theorem inputList2975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2975 (by decide) v hb
mask_input "2975|2305913377957871616|324518553658426728894218345906176"
def inputClause2977 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,false),(61,true)]
theorem inputList2977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2977 (by decide) v hb
mask_input "2977|2181431069507584|324518553658429032626165234270208"
def inputClause2978 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,false),(61,true)]
theorem inputList2978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2978 (by decide) v hb
mask_input "2978|2111062325329920|324518553658429032696533978447872"
def inputClause2979 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,false),(61,true)]
theorem inputList2979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2979 (by decide) v hb
mask_input "2979|2040693581152256|324518553658429032766902722625536"
def inputClause2980 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,false),(61,true)]
theorem inputList2980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2980 (by decide) v hb
mask_input "2980|1970324836974592|324518553658429032837271466803200"
def inputClause2981 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,false),(50,false),(61,true)]
theorem inputList2981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2981 (by decide) v hb
mask_input "2981|1899956092796928|324518553658429032907640210980864"
def inputClause2982 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,false),(50,false),(61,true)]
theorem inputList2982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2982 (by decide) v hb
mask_input "2982|1829587348619264|324518553658429032978008955158528"
def inputClause2983 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,false),(61,true)]
theorem inputList2983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2983 (by decide) v hb
mask_input "2983|1759218604441600|324518553658429033048377699336192"
def inputClause2984 : CNF.NClause := [(108,true),(46,true),(47,true),(48,true),(49,false),(50,false),(61,true)]
theorem inputList2984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2984 (by decide) v hb
mask_input "2984|1688849860263936|324518553658429033118746443513856"
def inputClause2985 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,true),(50,false),(61,true)]
theorem inputList2985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2985 (by decide) v hb
mask_input "2985|1618481116086272|324518553658429033189115187691520"
def inputClause2986 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,true),(50,false),(61,true)]
theorem inputList2986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2986 (by decide) v hb
mask_input "2986|1548112371908608|324518553658429033259483931869184"
def inputClause2987 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,false),(61,true)]
theorem inputList2987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2987 (by decide) v hb
mask_input "2987|1477743627730944|324518553658429033329852676046848"
def inputClause2988 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,true),(50,false),(61,true)]
theorem inputList2988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2988 (by decide) v hb
mask_input "2988|1407374883553280|324518553658429033400221420224512"
def inputClause2989 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,false),(61,true)]
theorem inputList2989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2989 (by decide) v hb
mask_input "2989|1337006139375616|324518553658429033470590164402176"
def inputClause2990 : CNF.NClause := [(108,true),(46,true),(47,false),(48,true),(49,true),(50,false),(61,true)]
theorem inputList2990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2990 (by decide) v hb
mask_input "2990|1266637395197952|324518553658429033540958908579840"
def inputClause2991 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,true),(50,false),(61,true)]
theorem inputList2991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2991 (by decide) v hb
mask_input "2991|1196268651020288|324518553658429033611327652757504"
end Percolation.MaskChain
