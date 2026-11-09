import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4191 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4191 (by decide) v hb
mask_input "4191|77371252455336271476162562|157238349383845436696035328"
def inputClause4192 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,false),(87,true)]
theorem inputList4192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4192 (by decide) v hb
mask_input "4192|77371252455336271476162560|157238349383845436696035330"
def inputClause4193 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4193 (by decide) v hb
mask_input "4193|2495844473172906628612098|232113757366008801543585792"
def inputClause4194 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4194 (by decide) v hb
mask_input "4194|2495844473172906628612096|232113757366008801543585794"
def inputClause4195 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4195 (by decide) v hb
mask_input "4195|2495770686196611790405634|232113831152985096381792256"
def inputClause4196 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4196 (by decide) v hb
mask_input "4196|2495770686196611790405632|232113831152985096381792258"
def inputClause4197 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4197 (by decide) v hb
mask_input "4197|2493483289931471806005250|232116118549250236366192640"
def inputClause4198 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4198 (by decide) v hb
mask_input "4198|2493483289931471806005248|232116118549250236366192642"
def inputClause4199 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4199 (by decide) v hb
mask_input "4199|2493409502955176967798786|232116192336226531204399104"
def inputClause4200 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,true),(87,true)]
theorem inputList4200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4200 (by decide) v hb
mask_input "4200|2493409502955176967798784|232116192336226531204399106"
def inputClause4201 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4201 (by decide) v hb
mask_input "4201|2420286609446992305192962|232189315229734715867004928"
def inputClause4202 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4202 (by decide) v hb
mask_input "4202|2420286609446992305192960|232189315229734715867004930"
def inputClause4203 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4203 (by decide) v hb
mask_input "4203|2420212822470697466986498|232189389016711010705211392"
def inputClause4204 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4204 (by decide) v hb
mask_input "4204|2420212822470697466986496|232189389016711010705211394"
def inputClause4205 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4205 (by decide) v hb
mask_input "4205|2417925426205557482586114|232191676412976150689611776"
def inputClause4206 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4206 (by decide) v hb
mask_input "4206|2417925426205557482586112|232191676412976150689611778"
def inputClause4207 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4207 (by decide) v hb
mask_input "4207|2417851639229262644379650|232191750199952445527818240"
def inputClause4208 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,true),(87,true)]
theorem inputList4208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4208 (by decide) v hb
mask_input "4208|2417851639229262644379648|232191750199952445527818242"
def inputClause4209 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4209 (by decide) v hb
mask_input "4209|77992833943648279199746|234531609005238059892998144"
def inputClause4210 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4210 (by decide) v hb
mask_input "4210|77992833943648279199744|234531609005238059892998146"
def inputClause4211 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4211 (by decide) v hb
mask_input "4211|77919046967353440993282|234531682792214354731204608"
def inputClause4212 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4212 (by decide) v hb
mask_input "4212|77919046967353440993280|234531682792214354731204610"
def inputClause4213 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4213 (by decide) v hb
mask_input "4213|75631650702213456592898|234533970188479494715604992"
def inputClause4214 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4214 (by decide) v hb
mask_input "4214|75631650702213456592896|234533970188479494715604994"
def inputClause4215 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4215 (by decide) v hb
mask_input "4215|75557863725918618386434|234534043975455789553811456"
def inputClause4216 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem inputList4216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4216 (by decide) v hb
mask_input "4216|75557863725918618386432|234534043975455789553811458"
def inputClause4217 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,true),(87,true)]
theorem inputList4217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4217 (by decide) v hb
mask_input "4217|2434970217733955780610|234607166868963974216417280"
def inputClause4218 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,true),(87,true)]
theorem inputList4218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4218 (by decide) v hb
mask_input "4218|2434970217733955780608|234607166868963974216417282"
def inputClause4221 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inputList4221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4221 (by decide) v hb
mask_input "4221|73786976299133173762|234609528052205409039024128"
def inputClause4222 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inputList4222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4222 (by decide) v hb
mask_input "4222|73786976299133173760|234609528052205409039024130"
def inputClause4223 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inputList4223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4223 (by decide) v hb
mask_input "4223|4294967298|234609601839181703877230592"
def inputClause4224 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,true),(87,true)]
theorem inputList4224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4224 (by decide) v hb
mask_input "4224|4294967296|234609601839181703877230594"
def inputClause4225 : CNF.NClause := [(33,true),(2,false),(64,false),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4225 (by decide) v hb
mask_input "4225|174709279142799826741100548|8589934592"
def inputClause4227 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4227 (by decide) v hb
mask_input "4227|174709260696055761621483524|18446744073709551616"
def inputClause4229 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4229 (by decide) v hb
mask_input "4229|174708688846989476625383428|590295810358705651712"
def inputClause4230 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4230 (by decide) v hb
mask_input "4230|174708688846989476625383424|590295810358705651716"
def inputClause4231 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4231 (by decide) v hb
mask_input "4231|174708670400245402915831812|608742554432415203328"
def inputClause4232 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inputList4232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4232 (by decide) v hb
mask_input "4232|174708670400245402915831808|608742554432415203332"
def inputClause4233 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4233 (by decide) v hb
mask_input "4233|174690389676868356750180356|18889465931478580854784"
def inputClause4234 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inputList4234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) inputClause4234 (by decide) v hb
mask_input "4234|174690389676868356750180352|18889465931478580854788"
end Percolation.MaskChain
