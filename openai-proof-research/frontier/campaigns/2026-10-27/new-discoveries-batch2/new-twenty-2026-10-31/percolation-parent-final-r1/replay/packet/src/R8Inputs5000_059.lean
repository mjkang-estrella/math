import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7122 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7122 (by decide) v hb
mask_input "7122|19418527810913404668870656|2477089004390375178989731840"
def inputClause7123 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7123 (by decide) v hb
mask_input "7123|19418518587541367830872064|2477089013613747215827730432"
def inputClause7124 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7124 (by decide) v hb
mask_input "7124|19418518587541367814094848|2477089013613747215844507648"
def inputClause7125 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7125 (by decide) v hb
mask_input "7125|19418380236960815009234944|2477089151964327768649367552"
def inputClause7126 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7126 (by decide) v hb
mask_input "7126|19418380236960814992457728|2477089151964327768666144768"
def inputClause7127 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7127 (by decide) v hb
mask_input "7127|19418371013588778154459136|2477089161187699805504143360"
def inputClause7128 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7128 (by decide) v hb
mask_input "7128|19418371013588778137681920|2477089161187699805520920576"
def inputClause7129 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7129 (by decide) v hb
mask_input "7129|19342969947187490362228736|2477164562254101093296373760"
def inputClause7130 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7130 (by decide) v hb
mask_input "7130|19342969947187490345451520|2477164562254101093313150976"
def inputClause7131 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7131 (by decide) v hb
mask_input "7131|19342960723815453507452928|2477164571477473130151149568"
def inputClause7132 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7132 (by decide) v hb
mask_input "7132|19342960723815453490675712|2477164571477473130167926784"
def inputClause7133 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7133 (by decide) v hb
mask_input "7133|19342822373234900685815808|2477164709828053682972786688"
def inputClause7134 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7134 (by decide) v hb
mask_input "7134|19342822373234900669038592|2477164709828053682989563904"
def inputClause7135 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7135 (by decide) v hb
mask_input "7135|19342813149862863831040000|2477164719051425719827562496"
def inputClause7136 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inputList7136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7136 (by decide) v hb
mask_input "7136|19342813149862863814262784|2477164719051425719844339712"
def inputClause7137 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7137 (by decide) v hb
mask_input "7137|1284640516693967065055232|2495222891684594616593547264"
def inputClause7138 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7138 (by decide) v hb
mask_input "7138|1284640516693967048278016|2495222891684594616610324480"
def inputClause7139 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7139 (by decide) v hb
mask_input "7139|1284631293321930210279424|2495222900907966653448323072"
def inputClause7140 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7140 (by decide) v hb
mask_input "7140|1284631293321930193502208|2495222900907966653465100288"
def inputClause7141 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7141 (by decide) v hb
mask_input "7141|1284492942741377388642304|2495223039258547206269960192"
def inputClause7142 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7142 (by decide) v hb
mask_input "7142|1284492942741377371865088|2495223039258547206286737408"
def inputClause7143 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7143 (by decide) v hb
mask_input "7143|1284483719369340533866496|2495223048481919243124736000"
def inputClause7144 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inputList7144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7144 (by decide) v hb
mask_input "7144|1284483719369340517089280|2495223048481919243141513216"
def inputClause7146 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,true),(91,true)]
theorem inputList7146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7146 (by decide) v hb
mask_input "7146|1209082652968052724858880|2495298449548320530933743616"
def inputClause7147 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,true),(91,true)]
theorem inputList7147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7147 (by decide) v hb
mask_input "7147|1209073429596015886860288|2495298458771692567771742208"
def inputClause7148 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,true),(91,true)]
theorem inputList7148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7148 (by decide) v hb
mask_input "7148|1209073429596015870083072|2495298458771692567788519424"
def inputClause7149 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inputList7149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7149 (by decide) v hb
mask_input "7149|1208935079015463065223168|2495298597122273120593379328"
def inputClause7150 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inputList7150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7150 (by decide) v hb
mask_input "7150|1208935079015463048445952|2495298597122273120610156544"
def inputClause7151 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inputList7151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7151 (by decide) v hb
mask_input "7151|1208925855643426210447360|2495298606345645157448155136"
def inputClause7152 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inputList7152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7152 (by decide) v hb
mask_input "7152|1208925855643426193670144|2495298606345645157464932352"
def inputClause7153 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inputList7153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7153 (by decide) v hb
mask_input "7153|75714697079337890349056|2496431817504209245768253440"
def inputClause7154 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inputList7154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7154 (by decide) v hb
mask_input "7154|75714697079337873571840|2496431817504209245785030656"
def inputClause7155 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inputList7155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7155 (by decide) v hb
mask_input "7155|75705473707301035573248|2496431826727581282623029248"
def inputClause7156 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inputList7156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7156 (by decide) v hb
mask_input "7156|75705473707301018796032|2496431826727581282639806464"
def inputClause7158 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,true),(91,true)]
theorem inputList7158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7158 (by decide) v hb
mask_input "7158|75567123126748197158912|2496431965078161835461443584"
def inputClause7160 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,true),(91,true)]
theorem inputList7160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7160 (by decide) v hb
mask_input "7160|75557899754711342383104|2496431974301533872316219392"
def inputClause7161 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inputList7161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7161 (by decide) v hb
mask_input "7161|156833353423566929920|2496507375367935160091672576"
def inputClause7162 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inputList7162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7162 (by decide) v hb
mask_input "7162|156833353423550152704|2496507375367935160108449792"
def inputClause7163 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inputList7163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7163 (by decide) v hb
mask_input "7163|147609981386712154112|2496507384591307196946448384"
def inputClause7164 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inputList7164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7164 (by decide) v hb
mask_input "7164|147609981386695376896|2496507384591307196963225600"
end Percolation.MaskChain
