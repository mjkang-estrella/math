import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7082 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7082 (by decide) v hb
mask_input "7082|2477089161223728602523107328|19418370977559981135495168"
def inputClause7083 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7083 (by decide) v hb
mask_input "7083|2477089152000356565685108736|19418380200932017973493760"
def inputClause7084 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7084 (by decide) v hb
mask_input "7084|2477089152000356565668331520|19418380200932017990270976"
def inputClause7085 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7085 (by decide) v hb
mask_input "7085|2477089013649776012863471616|19418518551512570795130880"
def inputClause7086 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7086 (by decide) v hb
mask_input "7086|2477089013649776012846694400|19418518551512570811908096"
def inputClause7087 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7087 (by decide) v hb
mask_input "7087|2477089004426403976008695808|19418527774884607649906688"
def inputClause7088 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7088 (by decide) v hb
mask_input "7088|2477089004426403975991918592|19418527774884607666683904"
def inputClause7089 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7089 (by decide) v hb
mask_input "7089|2475955793267839887688597504|20551738933448695970004992"
def inputClause7090 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7090 (by decide) v hb
mask_input "7090|2475955793267839887671820288|20551738933448695986782208"
def inputClause7091 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7091 (by decide) v hb
mask_input "7091|2475955784044467850833821696|20551748156820732824780800"
def inputClause7092 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7092 (by decide) v hb
mask_input "7092|2475955784044467850817044480|20551748156820732841558016"
def inputClause7093 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7093 (by decide) v hb
mask_input "7093|2475955645693887298012184576|20551886507401285646417920"
def inputClause7094 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7094 (by decide) v hb
mask_input "7094|2475955645693887297995407360|20551886507401285663195136"
def inputClause7095 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7095 (by decide) v hb
mask_input "7095|2475955636470515261157408768|20551895730773322501193728"
def inputClause7096 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,true),(91,false)]
theorem inputList7096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7096 (by decide) v hb
mask_input "7096|2475955636470515261140631552|20551895730773322517970944"
def inputClause7097 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7097 (by decide) v hb
mask_input "7097|2475880235404113973365178368|20627296797174610293424128"
def inputClause7098 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7098 (by decide) v hb
mask_input "7098|2475880235404113973348401152|20627296797174610310201344"
def inputClause7099 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7099 (by decide) v hb
mask_input "7099|2475880226180741936510402560|20627306020546647148199936"
def inputClause7100 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7100 (by decide) v hb
mask_input "7100|2475880226180741936493625344|20627306020546647164977152"
def inputClause7101 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7101 (by decide) v hb
mask_input "7101|2475880087830161383688765440|20627444371127199969837056"
def inputClause7102 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7102 (by decide) v hb
mask_input "7102|2475880087830161383671988224|20627444371127199986614272"
def inputClause7103 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7103 (by decide) v hb
mask_input "7103|2475880078606789346833989632|20627453594499236824612864"
def inputClause7104 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,true),(91,false)]
theorem inputList7104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7104 (by decide) v hb
mask_input "7104|2475880078606789346817212416|20627453594499236841390080"
def inputClause7105 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7105 (by decide) v hb
mask_input "7105|20627453630528033860354048|2475880078570760549798248448"
def inputClause7106 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7106 (by decide) v hb
mask_input "7106|20627453630528033843576832|2475880078570760549815025664"
def inputClause7107 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7107 (by decide) v hb
mask_input "7107|20627444407155997005578240|2475880087794132586653024256"
def inputClause7108 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7108 (by decide) v hb
mask_input "7108|20627444407155996988801024|2475880087794132586669801472"
def inputClause7109 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7109 (by decide) v hb
mask_input "7109|20627306056575444183941120|2475880226144713139474661376"
def inputClause7110 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7110 (by decide) v hb
mask_input "7110|20627306056575444167163904|2475880226144713139491438592"
def inputClause7111 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7111 (by decide) v hb
mask_input "7111|20627296833203407329165312|2475880235368085176329437184"
def inputClause7112 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,false),(91,true)]
theorem inputList7112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7112 (by decide) v hb
mask_input "7112|20627296833203407312388096|2475880235368085176346214400"
def inputClause7113 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7113 (by decide) v hb
mask_input "7113|20551895766802119536934912|2475955636434486464121667584"
def inputClause7114 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7114 (by decide) v hb
mask_input "7114|20551895766802119520157696|2475955636434486464138444800"
def inputClause7115 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7115 (by decide) v hb
mask_input "7115|20551886543430082682159104|2475955645657858500976443392"
def inputClause7116 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7116 (by decide) v hb
mask_input "7116|20551886543430082665381888|2475955645657858500993220608"
def inputClause7117 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7117 (by decide) v hb
mask_input "7117|20551748192849529860521984|2475955784008439053798080512"
def inputClause7118 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7118 (by decide) v hb
mask_input "7118|20551748192849529843744768|2475955784008439053814857728"
def inputClause7119 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7119 (by decide) v hb
mask_input "7119|20551738969477493005746176|2475955793231811090652856320"
def inputClause7120 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inputList7120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7120 (by decide) v hb
mask_input "7120|20551738969477492988968960|2475955793231811090669633536"
def inputClause7121 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inputList7121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7121 (by decide) v hb
mask_input "7121|19418527810913404685647872|2477089004390375178972954624"
end Percolation.MaskChain
