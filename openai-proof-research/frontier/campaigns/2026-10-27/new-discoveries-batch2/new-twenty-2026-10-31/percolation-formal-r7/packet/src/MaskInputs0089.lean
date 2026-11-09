import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5136 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5136 (by decide) v hb
mask_input "5136|316738564739033943284645888|38378451045352722137600"
def inputClause5137 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5137 (by decide) v hb
mask_input "5137|314359091550850037657371136|2417851639229258349412352"
def inputClause5138 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5138 (by decide) v hb
mask_input "5138|314359091550850037657370624|2417851639229258349412864"
def inputClause5139 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5139 (by decide) v hb
mask_input "5139|314359082327478000802595328|2417860862601295204188160"
def inputClause5140 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5140 (by decide) v hb
mask_input "5140|314359082327478000802594816|2417860862601295204188672"
def inputClause5141 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5141 (by decide) v hb
mask_input "5141|314358501255039678951719424|2418441935039617055064064"
def inputClause5142 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5142 (by decide) v hb
mask_input "5142|314358501255039678951718912|2418441935039617055064576"
def inputClause5143 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5143 (by decide) v hb
mask_input "5143|314358492031667642096943616|2418451158411653909839872"
def inputClause5144 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inputList5144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5144 (by decide) v hb
mask_input "5144|314358492031667642096943104|2418451158411653909840384"
def inputClause5145 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5145 (by decide) v hb
mask_input "5145|314321312618987080495661568|2455630571092215511121920"
def inputClause5146 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5146 (by decide) v hb
mask_input "5146|314321312618987080495661056|2455630571092215511122432"
def inputClause5147 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5147 (by decide) v hb
mask_input "5147|314321303395615043640885760|2455639794464252365897728"
def inputClause5148 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5148 (by decide) v hb
mask_input "5148|314321303395615043640885248|2455639794464252365898240"
def inputClause5149 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5149 (by decide) v hb
mask_input "5149|314320722323176721790009856|2456220866902574216773632"
def inputClause5150 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5150 (by decide) v hb
mask_input "5150|314320722323176721790009344|2456220866902574216774144"
def inputClause5151 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5151 (by decide) v hb
mask_input "5151|314320713099804684935234048|2456230090274611071549440"
def inputClause5152 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,false),(88,false)]
theorem inputList5152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5152 (by decide) v hb
mask_input "5152|314320713099804684935233536|2456230090274611071549952"
def inputClause5153 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5153 (by decide) v hb
mask_input "5153|311941239911620779307958784|4835703278458516698824704"
def inputClause5154 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5154 (by decide) v hb
mask_input "5154|311941239911620779307958272|4835703278458516698825216"
def inputClause5155 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5155 (by decide) v hb
mask_input "5155|311941230688248742453182976|4835712501830553553600512"
def inputClause5156 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5156 (by decide) v hb
mask_input "5156|311941230688248742453182464|4835712501830553553601024"
def inputClause5157 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5157 (by decide) v hb
mask_input "5157|311940649615810420602307072|4836293574268875404476416"
def inputClause5158 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5158 (by decide) v hb
mask_input "5158|311940649615810420602306560|4836293574268875404476928"
def inputClause5159 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5159 (by decide) v hb
mask_input "5159|311940640392438383747531264|4836302797640912259252224"
def inputClause5160 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,true),(88,false)]
theorem inputList5160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5160 (by decide) v hb
mask_input "5160|311940640392438383747530752|4836302797640912259252736"
def inputClause5161 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5161 (by decide) v hb
mask_input "5161|311903460979757822146249216|4873482210321473860534272"
def inputClause5162 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5162 (by decide) v hb
mask_input "5162|311903460979757822146248704|4873482210321473860534784"
def inputClause5163 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5163 (by decide) v hb
mask_input "5163|311903451756385785291473408|4873491433693510715310080"
def inputClause5164 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5164 (by decide) v hb
mask_input "5164|311903451756385785291472896|4873491433693510715310592"
def inputClause5165 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5165 (by decide) v hb
mask_input "5165|311902870683947463440597504|4874072506131832566185984"
def inputClause5166 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5166 (by decide) v hb
mask_input "5166|311902870683947463440596992|4874072506131832566186496"
def inputClause5167 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5167 (by decide) v hb
mask_input "5167|311902861460575426585821696|4874081729503869420961792"
def inputClause5168 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inputList5168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5168 (by decide) v hb
mask_input "5168|311902861460575426585821184|4874081729503869420962304"
def inputClause5169 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5169 (by decide) v hb
mask_input "5169|309523388272391520958546432|7253554917687775048237056"
def inputClause5170 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5170 (by decide) v hb
mask_input "5170|309523388272391520958545920|7253554917687775048237568"
def inputClause5171 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5171 (by decide) v hb
mask_input "5171|309523379049019484103770624|7253564141059811903012864"
def inputClause5172 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5172 (by decide) v hb
mask_input "5172|309523379049019484103770112|7253564141059811903013376"
def inputClause5173 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5173 (by decide) v hb
mask_input "5173|309522797976581162252894720|7254145213498133753888768"
def inputClause5174 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5174 (by decide) v hb
mask_input "5174|309522797976581162252894208|7254145213498133753889280"
def inputClause5175 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5175 (by decide) v hb
mask_input "5175|309522788753209125398118912|7254154436870170608664576"
end Percolation.MaskChain
