import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5315 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5315 (by decide) v hb
mask_input "5315|141670994488288379667456|4951764879508003969241710592"
def inputClause5316 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5316 (by decide) v hb
mask_input "5316|141670994488288379666432|4951764879508003969241711616"
def inputClause5317 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5317 (by decide) v hb
mask_input "5317|136948628005418734453760|4951769601874486838886924288"
def inputClause5318 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5318 (by decide) v hb
mask_input "5318|136948628005418734452736|4951769601874486838886925312"
def inputClause5319 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5319 (by decide) v hb
mask_input "5319|132226261522549089240064|4951774324240969708532137984"
def inputClause5320 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,false),(92,true)]
theorem inputList5320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5320 (by decide) v hb
mask_input "5320|132226261522549089239040|4951774324240969708532139008"
def inputClause5321 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5321 (by decide) v hb
mask_input "5321|127503895039679444026368|4951779046607452578177351680"
def inputClause5322 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5322 (by decide) v hb
mask_input "5322|127503895039679444025344|4951779046607452578177352704"
def inputClause5323 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5323 (by decide) v hb
mask_input "5323|122781528556809798812672|4951783768973935447822565376"
def inputClause5324 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5324 (by decide) v hb
mask_input "5324|122781528556809798811648|4951783768973935447822566400"
def inputClause5325 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5325 (by decide) v hb
mask_input "5325|118059162073940153598976|4951788491340418317467779072"
def inputClause5326 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5326 (by decide) v hb
mask_input "5326|118059162073940153597952|4951788491340418317467780096"
def inputClause5327 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5327 (by decide) v hb
mask_input "5327|113336795591070508385280|4951793213706901187112992768"
def inputClause5328 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,false),(92,true)]
theorem inputList5328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5328 (by decide) v hb
mask_input "5328|113336795591070508384256|4951793213706901187112993792"
def inputClause5329 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5329 (by decide) v hb
mask_input "5329|108614429108200863171584|4951797936073384056758206464"
def inputClause5330 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5330 (by decide) v hb
mask_input "5330|108614429108200863170560|4951797936073384056758207488"
def inputClause5331 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5331 (by decide) v hb
mask_input "5331|103892062625331217957888|4951802658439866926403420160"
def inputClause5332 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5332 (by decide) v hb
mask_input "5332|103892062625331217956864|4951802658439866926403421184"
def inputClause5333 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5333 (by decide) v hb
mask_input "5333|99169696142461572744192|4951807380806349796048633856"
def inputClause5334 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5334 (by decide) v hb
mask_input "5334|99169696142461572743168|4951807380806349796048634880"
def inputClause5335 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5335 (by decide) v hb
mask_input "5335|94447329659591927530496|4951812103172832665693847552"
def inputClause5336 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,false),(92,true)]
theorem inputList5336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5336 (by decide) v hb
mask_input "5336|94447329659591927529472|4951812103172832665693848576"
def inputClause5337 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5337 (by decide) v hb
mask_input "5337|89724963176722282316800|4951816825539315535339061248"
def inputClause5338 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5338 (by decide) v hb
mask_input "5338|89724963176722282315776|4951816825539315535339062272"
def inputClause5339 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5339 (by decide) v hb
mask_input "5339|85002596693852637103104|4951821547905798404984274944"
def inputClause5340 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5340 (by decide) v hb
mask_input "5340|85002596693852637102080|4951821547905798404984275968"
def inputClause5341 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5341 (by decide) v hb
mask_input "5341|80280230210982991889408|4951826270272281274629488640"
def inputClause5342 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5342 (by decide) v hb
mask_input "5342|80280230210982991888384|4951826270272281274629489664"
def inputClause5343 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5343 (by decide) v hb
mask_input "5343|75557863728113346675712|4951830992638764144274702336"
def inputClause5344 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,false),(92,true)]
theorem inputList5344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5344 (by decide) v hb
mask_input "5344|75557863728113346674688|4951830992638764144274703360"
def inputClause5345 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inputList5345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5345 (by decide) v hb
mask_input "5345|70835497245243701462016|4951835715005247013919916032"
def inputClause5346 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inputList5346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5346 (by decide) v hb
mask_input "5346|70835497245243701460992|4951835715005247013919917056"
def inputClause5347 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inputList5347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5347 (by decide) v hb
mask_input "5347|66113130762374056248320|4951840437371729883565129728"
def inputClause5348 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,false),(76,true),(92,true)]
theorem inputList5348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5348 (by decide) v hb
mask_input "5348|66113130762374056247296|4951840437371729883565130752"
def inputClause5350 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,false),(76,true),(92,true)]
theorem inputList5350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5350 (by decide) v hb
mask_input "5350|61390764279504411033600|4951845159738212753210344448"
def inputClause5351 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,false),(76,true),(92,true)]
theorem inputList5351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5351 (by decide) v hb
mask_input "5351|56668397796634765820928|4951849882104695622855557120"
def inputClause5352 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,false),(76,true),(92,true)]
theorem inputList5352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5352 (by decide) v hb
mask_input "5352|56668397796634765819904|4951849882104695622855558144"
def inputClause5353 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5353 (by decide) v hb
mask_input "5353|51946031313765120607232|4951854604471178492500770816"
def inputClause5354 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5354 (by decide) v hb
mask_input "5354|51946031313765120606208|4951854604471178492500771840"
def inputClause5355 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inputList5355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) inputClause5355 (by decide) v hb
mask_input "5355|47223664830895475393536|4951859326837661362145984512"
end Percolation.MaskChain
