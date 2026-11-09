import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7224 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,true),(92,false)]
theorem inputList7224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7224 (by decide) v hb
mask_input "7224|4951760175660322767343976448|124515522497573027840"
def inputClause7226 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,true),(92,false)]
theorem inputList7226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7226 (by decide) v hb
mask_input "7226|4951760171048636748916588544|129127208516000415744"
def inputClause7228 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,true),(92,false)]
theorem inputList7228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7228 (by decide) v hb
mask_input "7228|4951760166436950730489200640|133738894534427803648"
def inputClause7230 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,true),(92,false)]
theorem inputList7230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7230 (by decide) v hb
mask_input "7230|4951760161825264712061812736|138350580552855191552"
def inputClause7232 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,true),(92,false)]
theorem inputList7232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7232 (by decide) v hb
mask_input "7232|4951760157213578693634424832|142962266571282579456"
def inputClause7234 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,false),(92,true)]
theorem inputList7234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7234 (by decide) v hb
mask_input "7234|143034324165286952960|4951760157141521099630051328"
def inputClause7236 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,false),(92,true)]
theorem inputList7236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7236 (by decide) v hb
mask_input "7236|138422638146859565056|4951760161753207118057439232"
def inputClause7238 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,false),(92,true)]
theorem inputList7238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7238 (by decide) v hb
mask_input "7238|133810952128432177152|4951760166364893136484827136"
def inputClause7240 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,false),(92,true)]
theorem inputList7240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7240 (by decide) v hb
mask_input "7240|129199266110004789248|4951760170976579154912215040"
def inputClause7242 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,false),(92,true)]
theorem inputList7242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7242 (by decide) v hb
mask_input "7242|124587580091577401344|4951760175588265173339602944"
def inputClause7244 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,false),(92,true)]
theorem inputList7244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7244 (by decide) v hb
mask_input "7244|119975894073150013440|4951760180199951191766990848"
def inputClause7246 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,false),(92,true)]
theorem inputList7246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7246 (by decide) v hb
mask_input "7246|115364208054722625536|4951760184811637210194378752"
def inputClause7248 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,false),(92,true)]
theorem inputList7248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7248 (by decide) v hb
mask_input "7248|110752522036295237632|4951760189423323228621766656"
def inputClause7250 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,false),(92,true)]
theorem inputList7250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7250 (by decide) v hb
mask_input "7250|106140836017867849728|4951760194035009247049154560"
def inputClause7252 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,false),(92,true)]
theorem inputList7252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7252 (by decide) v hb
mask_input "7252|101529149999440461824|4951760198646695265476542464"
def inputClause7254 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,false),(92,true)]
theorem inputList7254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7254 (by decide) v hb
mask_input "7254|96917463981013073920|4951760203258381283903930368"
def inputClause7256 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,false),(92,true)]
theorem inputList7256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7256 (by decide) v hb
mask_input "7256|92305777962585686016|4951760207870067302331318272"
def inputClause7258 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,false),(92,true)]
theorem inputList7258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7258 (by decide) v hb
mask_input "7258|87694091944158298112|4951760212481753320758706176"
def inputClause7260 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,false),(92,true)]
theorem inputList7260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7260 (by decide) v hb
mask_input "7260|83082405925730910208|4951760217093439339186094080"
def inputClause7262 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,false),(92,true)]
theorem inputList7262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7262 (by decide) v hb
mask_input "7262|78470719907303522304|4951760221705125357613481984"
def inputClause7264 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,false),(92,true)]
theorem inputList7264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7264 (by decide) v hb
mask_input "7264|73859033888876134400|4951760226316811376040869888"
def inputClause7266 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,true),(92,true)]
theorem inputList7266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7266 (by decide) v hb
mask_input "7266|69247347870448746496|4951760230928497394468257792"
def inputClause7268 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,true),(92,true)]
theorem inputList7268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7268 (by decide) v hb
mask_input "7268|64635661852021358592|4951760235540183412895645696"
def inputClause7270 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,true),(92,true)]
theorem inputList7270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7270 (by decide) v hb
mask_input "7270|60023975833593970688|4951760240151869431323033600"
def inputClause7272 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,true),(92,true)]
theorem inputList7272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7272 (by decide) v hb
mask_input "7272|55412289815166582784|4951760244763555449750421504"
def inputClause7274 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,true),(92,true)]
theorem inputList7274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7274 (by decide) v hb
mask_input "7274|50800603796739194880|4951760249375241468177809408"
def inputClause7276 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,true),(92,true)]
theorem inputList7276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7276 (by decide) v hb
mask_input "7276|46188917778311806976|4951760253986927486605197312"
def inputClause7278 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,true),(92,true)]
theorem inputList7278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7278 (by decide) v hb
mask_input "7278|41577231759884419072|4951760258598613505032585216"
def inputClause7280 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,true),(92,true)]
theorem inputList7280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7280 (by decide) v hb
mask_input "7280|36965545741457031168|4951760263210299523459973120"
def inputClause7282 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,true),(92,true)]
theorem inputList7282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7282 (by decide) v hb
mask_input "7282|32353859723029643264|4951760267821985541887361024"
def inputClause7284 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,true),(92,true)]
theorem inputList7284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7284 (by decide) v hb
mask_input "7284|27742173704602255360|4951760272433671560314748928"
def inputClause7286 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,true),(92,true)]
theorem inputList7286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7286 (by decide) v hb
mask_input "7286|23130487686174867456|4951760277045357578742136832"
def inputClause7288 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,true),(92,true)]
theorem inputList7288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7288 (by decide) v hb
mask_input "7288|18518801667747479552|4951760281657043597169524736"
def inputClause7290 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,true),(92,true)]
theorem inputList7290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7290 (by decide) v hb
mask_input "7290|13907115649320091648|4951760286268729615596912640"
def inputClause7292 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,true),(92,true)]
theorem inputList7292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7292 (by decide) v hb
mask_input "7292|9295429630892703744|4951760290880415634024300544"
def inputClause7294 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,true),(92,true)]
theorem inputList7294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7294 (by decide) v hb
mask_input "7294|4683743612465315840|4951760295492101652451688448"
def inputClause7296 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,true),(92,true)]
theorem inputList7296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) inputClause7296 (by decide) v hb
mask_input "7296|72057594037927936|4951760300103787670879076352"
def inputClause7300 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inputList7300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7300 (by decide) v hb
mask_input "7300|2486196088296704477843423232|4611686018494496768"
def inputClause7308 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inputList7308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7308 (by decide) v hb
mask_input "7308|2486158309364841520681713664|37783543548975656206336"
def inputClause7316 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inputList7316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7316 (by decide) v hb
mask_input "7316|2485591625386897163256070144|604467521493333081849856"
end Percolation.MaskChain
