import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2129 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,true),(56,false)]
theorem inputList2129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2129 (by decide) v hb
mask_input "2129|72348148575502336|39614081257141175996026716160"
def inputClause2130 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,true),(56,false)]
theorem inputList2130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2130 (by decide) v hb
mask_input "2130|72348139985567744|39614081257141176004616650752"
def inputClause2131 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,true),(56,false)]
theorem inputList2131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2131 (by decide) v hb
mask_input "2131|72347873697595392|39614081257141176270904623104"
def inputClause2132 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,true),(56,false)]
theorem inputList2132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2132 (by decide) v hb
mask_input "2132|72347865107660800|39614081257141176279494557696"
def inputClause2133 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,true),(56,false)]
theorem inputList2133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2133 (by decide) v hb
mask_input "2133|72339352482480128|39614081257141184792119738368"
def inputClause2134 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,true),(56,false)]
theorem inputList2134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2134 (by decide) v hb
mask_input "2134|72339343892545536|39614081257141184800709672960"
def inputClause2137 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,true),(56,false)]
theorem inputList2137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2137 (by decide) v hb
mask_input "2137|72066673598791680|39614081257141457471003426816"
def inputClause2139 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,true),(56,false)]
theorem inputList2139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2139 (by decide) v hb
mask_input "2139|72066398720884736|39614081257141457745881333760"
def inputClause2140 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,true),(56,false)]
theorem inputList2140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2140 (by decide) v hb
mask_input "2140|72066390130950144|39614081257141457754471268352"
def inputClause2141 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,true),(56,false)]
theorem inputList2141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2141 (by decide) v hb
mask_input "2141|72057877505769472|39614081257141466267096449024"
def inputClause2145 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,false),(56,true)]
theorem inputList2145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2145 (by decide) v hb
mask_input "2145|9297753792315392|39614081257204226390809903104"
def inputClause2146 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,false),(56,true)]
theorem inputList2146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2146 (by decide) v hb
mask_input "2146|9297745202380800|39614081257204226399399837696"
def inputClause2147 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,false),(56,true)]
theorem inputList2147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2147 (by decide) v hb
mask_input "2147|9297478914408448|39614081257204226665687810048"
def inputClause2148 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,false),(56,true)]
theorem inputList2148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2148 (by decide) v hb
mask_input "2148|9297470324473856|39614081257204226674277744640"
def inputClause2149 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,false),(56,true)]
theorem inputList2149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2149 (by decide) v hb
mask_input "2149|9288957699293184|39614081257204235186902925312"
def inputClause2150 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,false),(56,true)]
theorem inputList2150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2150 (by decide) v hb
mask_input "2150|9288949109358592|39614081257204235195492859904"
def inputClause2151 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,false),(56,true)]
theorem inputList2151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2151 (by decide) v hb
mask_input "2151|9288682821386240|39614081257204235461780832256"
def inputClause2152 : CNF.NClause := [(95,true),(33,true),(38,true),(43,true),(48,false),(53,false),(56,true)]
theorem inputList2152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2152 (by decide) v hb
mask_input "2152|9288674231451648|39614081257204235470370766848"
def inputClause2153 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,false),(56,true)]
theorem inputList2153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2153 (by decide) v hb
mask_input "2153|9016278815604736|39614081257204507865786613760"
def inputClause2154 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,true),(53,false),(56,true)]
theorem inputList2154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2154 (by decide) v hb
mask_input "2154|9016270225670144|39614081257204507874376548352"
def inputClause2155 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,false),(56,true)]
theorem inputList2155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2155 (by decide) v hb
mask_input "2155|9016003937697792|39614081257204508140664520704"
def inputClause2156 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,true),(53,false),(56,true)]
theorem inputList2156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2156 (by decide) v hb
mask_input "2156|9015995347763200|39614081257204508149254455296"
def inputClause2157 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,false),(56,true)]
theorem inputList2157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2157 (by decide) v hb
mask_input "2157|9007482722582528|39614081257204516661879635968"
def inputClause2158 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,true),(53,false),(56,true)]
theorem inputList2158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2158 (by decide) v hb
mask_input "2158|9007474132647936|39614081257204516670469570560"
def inputClause2159 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,true),(53,false),(56,true)]
theorem inputList2159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2159 (by decide) v hb
mask_input "2159|9007207844675584|39614081257204516936757542912"
def inputClause2161 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,false),(53,true),(56,true)]
theorem inputList2161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2161 (by decide) v hb
mask_input "2161|290554537574400|39614081257213233590064644096"
def inputClause2162 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,false),(53,true),(56,true)]
theorem inputList2162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2162 (by decide) v hb
mask_input "2162|290545947639808|39614081257213233598654578688"
def inputClause2163 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,true),(56,true)]
theorem inputList2163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2163 (by decide) v hb
mask_input "2163|290279659667456|39614081257213233864942551040"
def inputClause2164 : CNF.NClause := [(95,true),(33,true),(38,true),(43,false),(48,false),(53,true),(56,true)]
theorem inputList2164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2164 (by decide) v hb
mask_input "2164|290271069732864|39614081257213233873532485632"
def inputClause2165 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,false),(53,true),(56,true)]
theorem inputList2165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2165 (by decide) v hb
mask_input "2165|281758444552192|39614081257213242386157666304"
def inputClause2166 : CNF.NClause := [(95,true),(33,true),(38,false),(43,true),(48,false),(53,true),(56,true)]
theorem inputList2166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2166 (by decide) v hb
mask_input "2166|281749854617600|39614081257213242394747600896"
def inputClause2167 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(48,false),(53,true),(56,true)]
theorem inputList2167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2167 (by decide) v hb
mask_input "2167|281483566645248|39614081257213242661035573248"
def inputClause2169 : CNF.NClause := [(95,true),(33,false),(38,false),(43,false),(48,true),(53,true),(56,true)]
theorem inputList2169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2169 (by decide) v hb
mask_input "2169|9079560863744|39614081257213515065041354752"
def inputClause2170 : CNF.NClause := [(95,true),(33,true),(38,false),(43,false),(48,true),(53,true),(56,true)]
theorem inputList2170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2170 (by decide) v hb
mask_input "2170|9070970929152|39614081257213515073631289344"
def inputClause2171 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,true),(56,true)]
theorem inputList2171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2171 (by decide) v hb
mask_input "2171|8804682956800|39614081257213515339919261696"
def inputClause2173 : CNF.NClause := [(95,true),(33,false),(38,false),(43,true),(48,true),(53,true),(56,true)]
theorem inputList2173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2173 (by decide) v hb
mask_input "2173|283467841536|39614081257213523861134376960"
def inputClause2175 : CNF.NClause := [(95,false),(33,false),(38,true),(43,true),(48,true),(53,true),(56,true)]
theorem inputList2175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2175 (by decide) v hb
mask_input "2175|39614081257132168805361909760|81355339240308736"
def inputClause2176 : CNF.NClause := [(95,false),(33,true),(38,true),(43,true),(48,true),(53,true),(56,true)]
theorem inputList2176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2176 (by decide) v hb
mask_input "2176|39614081257132168796771975168|81355347830243328"
def inputClause2178 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(54,false),(56,false)]
theorem inputList2178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2178 (by decide) v hb
mask_input "2178|90653084442689536|79228162514264337610723819520"
def inputClause2180 : CNF.NClause := [(96,true),(34,true),(39,true),(44,false),(49,false),(54,false),(56,false)]
theorem inputList2180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2180 (by decide) v hb
mask_input "2180|90652534686875648|79228162514264338160479633408"
end Percolation.MaskChain
