import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5092 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5092 (by decide) v hb
mask_input "5092|680315921438958019411968|1242775779457326939017052416"
def inputClause5093 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5093 (by decide) v hb
mask_input "5093|680057667021926085689600|1242776037711743970950774784"
def inputClause5094 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5094 (by decide) v hb
mask_input "5094|680057667021926085689344|1242776037711743970950775040"
def inputClause5095 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5095 (by decide) v hb
mask_input "5095|680020773533778666586368|1242776074605232118369878016"
def inputClause5096 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inputList5096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5096 (by decide) v hb
mask_input "5096|680020773533778666586112|1242776074605232118369878272"
def inputClause5097 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inputList5097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5097 (by decide) v hb
mask_input "5097|604794951201191115096320|1242851300427564705921368064"
def inputClause5098 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inputList5098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5098 (by decide) v hb
mask_input "5098|604794951201191115096064|1242851300427564705921368320"
def inputClause5099 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inputList5099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5099 (by decide) v hb
mask_input "5099|604758057713043695993088|1242851337321052853340471296"
def inputClause5100 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inputList5100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5100 (by decide) v hb
mask_input "5100|604758057713043695992832|1242851337321052853340471552"
def inputClause5101 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,true),(90,true)]
theorem inputList5101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5101 (by decide) v hb
mask_input "5101|604499803296011762270464|1242851595575469885274193920"
def inputClause5102 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,true),(90,true)]
theorem inputList5102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5102 (by decide) v hb
mask_input "5102|604499803296011762270208|1242851595575469885274194176"
def inputClause5104 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,true),(90,true)]
theorem inputList5104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5104 (by decide) v hb
mask_input "5104|604462909807864343166976|1242851632468958032693297408"
def inputClause5105 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inputList5105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5105 (by decide) v hb
mask_input "5105|75889905119790851162368|1243380205473646106185302016"
def inputClause5106 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inputList5106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5106 (by decide) v hb
mask_input "5106|75889905119790851162112|1243380205473646106185302272"
def inputClause5107 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inputList5107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5107 (by decide) v hb
mask_input "5107|75853011631643432059136|1243380242367134253604405248"
def inputClause5108 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inputList5108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5108 (by decide) v hb
mask_input "5108|75853011631643432058880|1243380242367134253604405504"
def inputClause5109 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,true),(90,true)]
theorem inputList5109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5109 (by decide) v hb
mask_input "5109|75594757214611498336512|1243380500621551285538127872"
def inputClause5110 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,true),(90,true)]
theorem inputList5110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5110 (by decide) v hb
mask_input "5110|75594757214611498336256|1243380500621551285538128128"
def inputClause5112 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,true),(90,true)]
theorem inputList5112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5112 (by decide) v hb
mask_input "5112|75557863726464079233024|1243380537515039432957231360"
def inputClause5113 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inputList5113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5113 (by decide) v hb
mask_input "5113|332041393876527743232|1243455763337372020508721152"
def inputClause5114 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inputList5114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5114 (by decide) v hb
mask_input "5114|332041393876527742976|1243455763337372020508721408"
def inputClause5115 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inputList5115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5115 (by decide) v hb
mask_input "5115|295147905729108640000|1243455800230860167927824384"
def inputClause5116 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inputList5116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5116 (by decide) v hb
mask_input "5116|295147905729108639744|1243455800230860167927824640"
def inputClause5117 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,true),(90,true)]
theorem inputList5117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5117 (by decide) v hb
mask_input "5117|36893488697174917376|1243456058485277199861547008"
def inputClause5118 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,true),(90,true)]
theorem inputList5118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5118 (by decide) v hb
mask_input "5118|36893488697174917120|1243456058485277199861547264"
def inputClause5120 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,true),(90,true)]
theorem inputList5120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5120 (by decide) v hb
mask_input "5120|549755813888|1243456095378765347280650496"
def inputClause5122 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5122 (by decide) v hb
mask_input "5122|316776943190079296006782976|512"
def inputClause5123 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5123 (by decide) v hb
mask_input "5123|316776933966707259152007680|9223372036854775808"
def inputClause5124 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5124 (by decide) v hb
mask_input "5124|316776933966707259152007168|9223372036854776320"
def inputClause5125 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5125 (by decide) v hb
mask_input "5125|316776352894268937301131776|590295810358705651712"
def inputClause5126 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5126 (by decide) v hb
mask_input "5126|316776352894268937301131264|590295810358705652224"
def inputClause5127 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5127 (by decide) v hb
mask_input "5127|316776343670896900446355968|599519182395560427520"
def inputClause5128 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inputList5128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5128 (by decide) v hb
mask_input "5128|316776343670896900446355456|599519182395560428032"
def inputClause5129 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5129 (by decide) v hb
mask_input "5129|316739164258216338845073920|37778931862957161709568"
def inputClause5130 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5130 (by decide) v hb
mask_input "5130|316739164258216338845073408|37778931862957161710080"
def inputClause5131 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5131 (by decide) v hb
mask_input "5131|316739155034844301990298112|37788155234994016485376"
def inputClause5132 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5132 (by decide) v hb
mask_input "5132|316739155034844301990297600|37788155234994016485888"
def inputClause5133 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5133 (by decide) v hb
mask_input "5133|316738573962405980139422208|38369227673315867361280"
def inputClause5134 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5134 (by decide) v hb
mask_input "5134|316738573962405980139421696|38369227673315867361792"
def inputClause5135 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inputList5135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) inputClause5135 (by decide) v hb
mask_input "5135|316738564739033943284646400|38378451045352722137088"
end Percolation.MaskChain
