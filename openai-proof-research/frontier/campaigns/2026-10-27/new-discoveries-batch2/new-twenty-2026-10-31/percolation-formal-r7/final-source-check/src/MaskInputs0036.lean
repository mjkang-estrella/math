import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2083 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,false),(56,true)]
theorem inputList2083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2083 (by decide) v hb
mask_input "2083|37189915657633792|19807040628638143091935543296"
def inputClause2084 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,false),(55,false),(56,true)]
theorem inputList2084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2084 (by decide) v hb
mask_input "2084|37189881297895424|19807040628638143126295281664"
def inputClause2085 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,false),(56,true)]
theorem inputList2085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2085 (by decide) v hb
mask_input "2085|37155830797172736|19807040628638177176796004352"
def inputClause2086 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,false),(56,true)]
theorem inputList2086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2086 (by decide) v hb
mask_input "2086|37155796437434368|19807040628638177211155742720"
def inputClause2087 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,false),(56,true)]
theorem inputList2087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2087 (by decide) v hb
mask_input "2087|37154731285544960|19807040628638178276307632128"
def inputClause2088 : CNF.NClause := [(94,true),(35,true),(40,true),(45,true),(50,false),(55,false),(56,true)]
theorem inputList2088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2088 (by decide) v hb
mask_input "2088|37154696925806592|19807040628638178310667370496"
def inputClause2089 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,true),(55,false),(56,true)]
theorem inputList2089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2089 (by decide) v hb
mask_input "2089|36065115262418944|19807040628639267892330758144"
def inputClause2090 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,false),(56,true)]
theorem inputList2090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2090 (by decide) v hb
mask_input "2090|36065080902680576|19807040628639267926690496512"
def inputClause2091 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,false),(56,true)]
theorem inputList2091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2091 (by decide) v hb
mask_input "2091|36064015750791168|19807040628639268991842385920"
def inputClause2092 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,true),(55,false),(56,true)]
theorem inputList2092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2092 (by decide) v hb
mask_input "2092|36063981391052800|19807040628639269026202124288"
def inputClause2093 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,false),(56,true)]
theorem inputList2093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2093 (by decide) v hb
mask_input "2093|36029930890330112|19807040628639303076702846976"
def inputClause2094 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,true),(55,false),(56,true)]
theorem inputList2094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2094 (by decide) v hb
mask_input "2094|36029896530591744|19807040628639303111062585344"
def inputClause2095 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,true),(55,false),(56,true)]
theorem inputList2095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2095 (by decide) v hb
mask_input "2095|36028831378702336|19807040628639304176214474752"
def inputClause2097 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,true),(56,true)]
theorem inputList2097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2097 (by decide) v hb
mask_input "2097|1162218150297600|19807040628674170789442879488"
def inputClause2098 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,true),(56,true)]
theorem inputList2098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2098 (by decide) v hb
mask_input "2098|1162183790559232|19807040628674170823802617856"
def inputClause2099 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,true),(56,true)]
theorem inputList2099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2099 (by decide) v hb
mask_input "2099|1161118638669824|19807040628674171888954507264"
def inputClause2100 : CNF.NClause := [(94,true),(35,true),(40,true),(45,false),(50,false),(55,true),(56,true)]
theorem inputList2100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2100 (by decide) v hb
mask_input "2100|1161084278931456|19807040628674171923314245632"
def inputClause2101 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,false),(55,true),(56,true)]
theorem inputList2101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2101 (by decide) v hb
mask_input "2101|1127033778208768|19807040628674205973814968320"
def inputClause2102 : CNF.NClause := [(94,true),(35,true),(40,false),(45,true),(50,false),(55,true),(56,true)]
theorem inputList2102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2102 (by decide) v hb
mask_input "2102|1126999418470400|19807040628674206008174706688"
def inputClause2103 : CNF.NClause := [(94,true),(35,false),(40,true),(45,true),(50,false),(55,true),(56,true)]
theorem inputList2103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2103 (by decide) v hb
mask_input "2103|1125934266580992|19807040628674207073326596096"
def inputClause2105 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,true),(55,true),(56,true)]
theorem inputList2105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2105 (by decide) v hb
mask_input "2105|36318243454976|19807040628675296689349722112"
def inputClause2106 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,true),(55,true),(56,true)]
theorem inputList2106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2106 (by decide) v hb
mask_input "2106|36283883716608|19807040628675296723709460480"
def inputClause2107 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,true),(55,true),(56,true)]
theorem inputList2107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2107 (by decide) v hb
mask_input "2107|35218731827200|19807040628675297788861349888"
def inputClause2109 : CNF.NClause := [(94,true),(35,false),(40,false),(45,true),(50,true),(55,true),(56,true)]
theorem inputList2109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2109 (by decide) v hb
mask_input "2109|1133871366144|19807040628675331873721810944"
def inputClause2111 : CNF.NClause := [(94,false),(35,false),(40,true),(45,true),(50,true),(55,true),(56,true)]
theorem inputList2111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2111 (by decide) v hb
mask_input "2111|19807040628566084432745725952|109248574847451136"
def inputClause2112 : CNF.NClause := [(94,false),(35,true),(40,true),(45,true),(50,true),(55,true),(56,true)]
theorem inputList2112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2112 (by decide) v hb
mask_input "2112|19807040628566084398385987584|109248609207189504"
def inputClause2113 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,false),(56,false)]
theorem inputList2113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2113 (by decide) v hb
mask_input "2113|81355347830243328|39614081257132168796771975168"
def inputClause2114 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,false),(56,false)]
theorem inputList2114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2114 (by decide) v hb
mask_input "2114|81355339240308736|39614081257132168805361909760"
def inputClause2115 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,false),(56,false)]
theorem inputList2115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2115 (by decide) v hb
mask_input "2115|81355072952336384|39614081257132169071649882112"
def inputClause2116 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,false),(56,false)]
theorem inputList2116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2116 (by decide) v hb
mask_input "2116|81355064362401792|39614081257132169080239816704"
def inputClause2117 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,false),(56,false)]
theorem inputList2117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2117 (by decide) v hb
mask_input "2117|81346551737221120|39614081257132177592864997376"
def inputClause2118 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,false),(56,false)]
theorem inputList2118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2118 (by decide) v hb
mask_input "2118|81346543147286528|39614081257132177601454931968"
def inputClause2119 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,false),(56,false)]
theorem inputList2119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2119 (by decide) v hb
mask_input "2119|81346276859314176|39614081257132177867742904320"
def inputClause2121 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,false),(56,false)]
theorem inputList2121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2121 (by decide) v hb
mask_input "2121|81073872853532672|39614081257132450271748685824"
def inputClause2122 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,true),(53,false),(56,false)]
theorem inputList2122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2122 (by decide) v hb
mask_input "2122|81073864263598080|39614081257132450280338620416"
def inputClause2123 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,false),(56,false)]
theorem inputList2123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2123 (by decide) v hb
mask_input "2123|81073597975625728|39614081257132450546626592768"
def inputClause2124 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,false),(56,false)]
theorem inputList2124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2124 (by decide) v hb
mask_input "2124|81073589385691136|39614081257132450555216527360"
def inputClause2125 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,false),(56,false)]
theorem inputList2125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2125 (by decide) v hb
mask_input "2125|81065076760510464|39614081257132459067841708032"
def inputClause2126 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,true),(53,false),(56,false)]
theorem inputList2126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2126 (by decide) v hb
mask_input "2126|81065068170575872|39614081257132459076431642624"
def inputClause2127 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,true),(53,false),(56,false)]
theorem inputList2127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2127 (by decide) v hb
mask_input "2127|81064801882603520|39614081257132459342719614976"
end Percolation.MaskChain
