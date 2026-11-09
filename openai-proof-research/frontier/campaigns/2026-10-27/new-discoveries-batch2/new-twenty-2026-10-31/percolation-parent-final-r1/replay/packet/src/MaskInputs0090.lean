import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5176 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,true),(88,false)]
theorem inputList5176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5176 (by decide) v hb
mask_input "5176|309522788753209125398118400|7254154436870170608665088"
def inputClause5177 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5177 (by decide) v hb
mask_input "5177|309485609340528563796836864|7291333849550732209946624"
def inputClause5178 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5178 (by decide) v hb
mask_input "5178|309485609340528563796836352|7291333849550732209947136"
def inputClause5179 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5179 (by decide) v hb
mask_input "5179|309485600117156526942061056|7291343072922769064722432"
def inputClause5180 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5180 (by decide) v hb
mask_input "5180|309485600117156526942060544|7291343072922769064722944"
def inputClause5181 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5181 (by decide) v hb
mask_input "5181|309485019044718205091185152|7291924145361090915598336"
def inputClause5182 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5182 (by decide) v hb
mask_input "5182|309485019044718205091184640|7291924145361090915598848"
def inputClause5183 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5183 (by decide) v hb
mask_input "5183|309485009821346168236409344|7291933368733127770374144"
def inputClause5184 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,true),(82,true),(88,false)]
theorem inputList5184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5184 (by decide) v hb
mask_input "5184|309485009821346168236408832|7291933368733127770374656"
def inputClause5185 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5185 (by decide) v hb
mask_input "5185|7291933368734227282002432|309485009821345068724781056"
def inputClause5186 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5186 (by decide) v hb
mask_input "5186|7291933368734227282001920|309485009821345068724781568"
def inputClause5187 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5187 (by decide) v hb
mask_input "5187|7291924145362190427226624|309485019044717105579556864"
def inputClause5188 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5188 (by decide) v hb
mask_input "5188|7291924145362190427226112|309485019044717105579557376"
def inputClause5189 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5189 (by decide) v hb
mask_input "5189|7291343072923868576350720|309485600117155427430432768"
def inputClause5190 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5190 (by decide) v hb
mask_input "5190|7291343072923868576350208|309485600117155427430433280"
def inputClause5191 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5191 (by decide) v hb
mask_input "5191|7291333849551831721574912|309485609340527464285208576"
def inputClause5192 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,false),(88,true)]
theorem inputList5192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5192 (by decide) v hb
mask_input "5192|7291333849551831721574400|309485609340527464285209088"
def inputClause5193 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5193 (by decide) v hb
mask_input "5193|7254154436871270120292864|309522788753208025886490624"
def inputClause5194 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5194 (by decide) v hb
mask_input "5194|7254154436871270120292352|309522788753208025886491136"
def inputClause5195 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5195 (by decide) v hb
mask_input "5195|7254145213499233265517056|309522797976580062741266432"
def inputClause5196 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5196 (by decide) v hb
mask_input "5196|7254145213499233265516544|309522797976580062741266944"
def inputClause5197 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5197 (by decide) v hb
mask_input "5197|7253564141060911414641152|309523379049018384592142336"
def inputClause5198 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5198 (by decide) v hb
mask_input "5198|7253564141060911414640640|309523379049018384592142848"
def inputClause5199 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5199 (by decide) v hb
mask_input "5199|7253554917688874559865344|309523388272390421446918144"
def inputClause5200 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,false),(88,true)]
theorem inputList5200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5200 (by decide) v hb
mask_input "5200|7253554917688874559864832|309523388272390421446918656"
def inputClause5201 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5201 (by decide) v hb
mask_input "5201|4874081729504968932590080|311902861460574327074193408"
def inputClause5202 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5202 (by decide) v hb
mask_input "5202|4874081729504968932589568|311902861460574327074193920"
def inputClause5203 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5203 (by decide) v hb
mask_input "5203|4874072506132932077814272|311902870683946363928969216"
def inputClause5204 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5204 (by decide) v hb
mask_input "5204|4874072506132932077813760|311902870683946363928969728"
def inputClause5205 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5205 (by decide) v hb
mask_input "5205|4873491433694610226938368|311903451756384685779845120"
def inputClause5206 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5206 (by decide) v hb
mask_input "5206|4873491433694610226937856|311903451756384685779845632"
def inputClause5207 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5207 (by decide) v hb
mask_input "5207|4873482210322573372162560|311903460979756722634620928"
def inputClause5208 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,false),(88,true)]
theorem inputList5208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5208 (by decide) v hb
mask_input "5208|4873482210322573372162048|311903460979756722634621440"
def inputClause5209 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5209 (by decide) v hb
mask_input "5209|4836302797642011770880512|311940640392437284235902976"
def inputClause5210 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5210 (by decide) v hb
mask_input "5210|4836302797642011770880000|311940640392437284235903488"
def inputClause5211 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5211 (by decide) v hb
mask_input "5211|4836293574269974916104704|311940649615809321090678784"
def inputClause5212 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5212 (by decide) v hb
mask_input "5212|4836293574269974916104192|311940649615809321090679296"
def inputClause5213 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5213 (by decide) v hb
mask_input "5213|4835712501831653065228800|311941230688247642941554688"
def inputClause5214 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5214 (by decide) v hb
mask_input "5214|4835712501831653065228288|311941230688247642941555200"
def inputClause5215 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,true),(82,false),(88,true)]
theorem inputList5215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5215 (by decide) v hb
mask_input "5215|4835703278459616210452992|311941239911619679796330496"
end Percolation.MaskChain
