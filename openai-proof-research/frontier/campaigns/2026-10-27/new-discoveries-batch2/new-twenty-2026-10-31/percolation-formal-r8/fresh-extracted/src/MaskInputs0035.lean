import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2025 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,false),(61,true)]
theorem inputList2025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2025 (by decide) v hb
mask_input "2025|1657324662872342528|9903520317165345960710111232"
def inputClause2026 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,false),(61,true)]
theorem inputList2026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2026 (by decide) v hb
mask_input "2026|1585267068834414592|9903520317237403554748039168"
def inputClause2027 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,true),(60,false),(61,true)]
theorem inputList2027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2027 (by decide) v hb
mask_input "2027|1513209474796486656|9903520317309461148785967104"
def inputClause2028 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,true),(60,false),(61,true)]
theorem inputList2028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2028 (by decide) v hb
mask_input "2028|1441151880758558720|9903520317381518742823895040"
def inputClause2029 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,false),(61,true)]
theorem inputList2029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2029 (by decide) v hb
mask_input "2029|1369094286720630784|9903520317453576336861822976"
def inputClause2030 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,true),(60,false),(61,true)]
theorem inputList2030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2030 (by decide) v hb
mask_input "2030|1297036692682702848|9903520317525633930899750912"
def inputClause2033 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,true),(61,true)]
theorem inputList2033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2033 (by decide) v hb
mask_input "2033|1080863910568919040|9903520317741806713013534720"
def inputClause2034 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,true),(61,true)]
theorem inputList2034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2034 (by decide) v hb
mask_input "2034|1008806316530991104|9903520317813864307051462656"
def inputClause2036 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,true),(61,true)]
theorem inputList2036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2036 (by decide) v hb
mask_input "2036|864691128455135232|9903520317957979495127318528"
def inputClause2037 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,true),(61,true)]
theorem inputList2037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2037 (by decide) v hb
mask_input "2037|792633534417207296|9903520318030037089165246464"
def inputClause2038 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,true),(61,true)]
theorem inputList2038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2038 (by decide) v hb
mask_input "2038|720575940379279360|9903520318102094683203174400"
def inputClause2041 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,true),(61,true)]
theorem inputList2041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2041 (by decide) v hb
mask_input "2041|504403158265495552|9903520318318267465316958208"
def inputClause2042 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,true),(61,true)]
theorem inputList2042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2042 (by decide) v hb
mask_input "2042|432345564227567616|9903520318390325059354886144"
def inputClause2048 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,true),(60,true),(61,true)]
theorem inputList2048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2048 (by decide) v hb
mask_input "2048|9903520314283042199192993792|4539628424389459968"
def inputClause2049 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,false),(56,false)]
theorem inputList2049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2049 (by decide) v hb
mask_input "2049|109248609207189504|19807040628566084398385987584"
def inputClause2050 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,false),(56,false)]
theorem inputList2050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2050 (by decide) v hb
mask_input "2050|109248574847451136|19807040628566084432745725952"
def inputClause2051 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,false),(56,false)]
theorem inputList2051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2051 (by decide) v hb
mask_input "2051|109247509695561728|19807040628566085497897615360"
def inputClause2052 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,false),(55,false),(56,false)]
theorem inputList2052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2052 (by decide) v hb
mask_input "2052|109247475335823360|19807040628566085532257353728"
def inputClause2053 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,false),(56,false)]
theorem inputList2053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2053 (by decide) v hb
mask_input "2053|109213424835100672|19807040628566119582758076416"
def inputClause2054 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,false),(56,false)]
theorem inputList2054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2054 (by decide) v hb
mask_input "2054|109213390475362304|19807040628566119617117814784"
def inputClause2055 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,false),(56,false)]
theorem inputList2055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2055 (by decide) v hb
mask_input "2055|109212325323472896|19807040628566120682269704192"
def inputClause2056 : CNF.NClause := [(94,true),(35,true),(40,true),(45,true),(50,false),(55,false),(56,false)]
theorem inputList2056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2056 (by decide) v hb
mask_input "2056|109212290963734528|19807040628566120716629442560"
def inputClause2057 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,true),(55,false),(56,false)]
theorem inputList2057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2057 (by decide) v hb
mask_input "2057|108122709300346880|19807040628567210298292830208"
def inputClause2058 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,false),(56,false)]
theorem inputList2058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2058 (by decide) v hb
mask_input "2058|108122674940608512|19807040628567210332652568576"
def inputClause2059 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,false),(56,false)]
theorem inputList2059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2059 (by decide) v hb
mask_input "2059|108121609788719104|19807040628567211397804457984"
def inputClause2060 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,true),(55,false),(56,false)]
theorem inputList2060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2060 (by decide) v hb
mask_input "2060|108121575428980736|19807040628567211432164196352"
def inputClause2061 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,false),(56,false)]
theorem inputList2061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2061 (by decide) v hb
mask_input "2061|108087524928258048|19807040628567245482664919040"
def inputClause2062 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,true),(55,false),(56,false)]
theorem inputList2062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2062 (by decide) v hb
mask_input "2062|108087490568519680|19807040628567245517024657408"
def inputClause2063 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,false),(56,false)]
theorem inputList2063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2063 (by decide) v hb
mask_input "2063|108086425416630272|19807040628567246582176546816"
def inputClause2065 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,true),(56,false)]
theorem inputList2065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2065 (by decide) v hb
mask_input "2065|73219812188225536|19807040628602113195404951552"
def inputClause2066 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,true),(56,false)]
theorem inputList2066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2066 (by decide) v hb
mask_input "2066|73219777828487168|19807040628602113229764689920"
def inputClause2067 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,true),(56,false)]
theorem inputList2067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2067 (by decide) v hb
mask_input "2067|73218712676597760|19807040628602114294916579328"
def inputClause2069 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,true),(56,false)]
theorem inputList2069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2069 (by decide) v hb
mask_input "2069|73184627816136704|19807040628602148379777040384"
def inputClause2070 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,true),(56,false)]
theorem inputList2070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2070 (by decide) v hb
mask_input "2070|73184593456398336|19807040628602148414136778752"
def inputClause2071 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,true),(56,false)]
theorem inputList2071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2071 (by decide) v hb
mask_input "2071|73183528304508928|19807040628602149479288668160"
def inputClause2074 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,true),(56,false)]
theorem inputList2074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2074 (by decide) v hb
mask_input "2074|72093877921644544|19807040628603239129671532544"
def inputClause2075 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,true),(56,false)]
theorem inputList2075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2075 (by decide) v hb
mask_input "2075|72092812769755136|19807040628603240194823421952"
def inputClause2077 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,true),(56,false)]
theorem inputList2077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2077 (by decide) v hb
mask_input "2077|72058727909294080|19807040628603274279683883008"
def inputClause2079 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,true),(56,false)]
theorem inputList2079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2079 (by decide) v hb
mask_input "2079|72057628397666304|19807040628603275379195510784"
def inputClause2082 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,false),(56,true)]
theorem inputList2082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2082 (by decide) v hb
mask_input "2082|37190980809523200|19807040628638142026783653888"
end Percolation.MaskChain
