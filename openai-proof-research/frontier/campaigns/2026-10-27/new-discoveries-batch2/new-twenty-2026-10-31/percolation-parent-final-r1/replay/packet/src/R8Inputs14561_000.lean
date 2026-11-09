import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause575 : CNF.NClause := [(70,false),(3,false),(6,true),(14,true),(17,true),(20,true),(28,true)]
theorem inputList575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause575 (by decide) v hb
mask_input "575|1180591620717411303432|269631552"
def inputClause1144 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,false),(21,true),(26,true)]
theorem inputList1144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1144 (by decide) v hb
mask_input "1144|604462909807314587385856|69222660"
def inputClause1568 : CNF.NClause := [(86,false),(1,true),(5,true),(14,true),(18,true),(22,true),(29,false)]
theorem inputList1568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1568 (by decide) v hb
mask_input "1568|77371252455336267718066176|4472866"
def inputClause1584 : CNF.NClause := [(86,false),(1,true),(5,true),(14,true),(18,true),(22,false),(29,true)]
theorem inputList1584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1584 (by decide) v hb
mask_input "1584|77371252455336267185389568|537149474"
def inputClause1592 : CNF.NClause := [(86,false),(1,true),(5,true),(14,true),(18,false),(22,true),(29,true)]
theorem inputList1592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1592 (by decide) v hb
mask_input "1592|77371252455336267181457408|541081634"
def inputClause1596 : CNF.NClause := [(86,false),(1,true),(5,true),(14,false),(18,true),(22,true),(29,true)]
theorem inputList1596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1596 (by decide) v hb
mask_input "1596|77371252455336267181211648|541327394"
def inputClause1599 : CNF.NClause := [(86,false),(1,false),(5,true),(14,true),(18,true),(22,true),(29,true)]
theorem inputList1599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1599 (by decide) v hb
mask_input "1599|77371252455336267181195266|541343776"
def inputClause8021 : CNF.NClause := [(127,false),(130,true),(138,true),(141,true),(144,true),(152,true)]
theorem inputList8021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) inputClause8021 (by decide) v hb
mask_input "8021|170141183460469231731687303715884105728|5734428919445381200007811909951149809946591232"
def inputClause8080 : CNF.NClause := [(127,true),(131,false),(135,true),(139,true),(148,true),(153,true)]
theorem inputList8080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) inputClause8080 (by decide) v hb
mask_input "8080|2722258935367507707706996859454145691648|11775534089395772441296587282791410118669893632"
def inputClause8095 : CNF.NClause := [(128,true),(129,true),(135,true),(141,true),(147,false),(150,true)]
theorem inputList8095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) inputClause8095 (by decide) v hb
mask_input "8095|178405961588244985132285746181186892047843328|1430079862845842851889691636307149743206694912"
def inputClause8157 : CNF.NClause := [(180,true),(181,true),(182,false),(183,true),(184,true),(185,true)]
theorem inputList8157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) inputClause8157 (by decide) v hb
mask_input "8157|6129982163463555433433388108601236734474956488734408704|90417236911087442643142474601868241833505608208832528384"
def inputClause8165 : CNF.NClause := [(159,false),(164,true),(169,true),(174,true),(179,true),(180,true)]
theorem inputList8165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) inputClause8165 (by decide) v hb
mask_input "8165|730750818665451459101842416358141509827966271488|2323460226989373517690181258616361553856529814442213376"
def inputClause8168 : CNF.NClause := [(157,true),(162,true),(167,true),(172,false),(177,true),(180,true)]
theorem inputList8168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) inputClause8168 (by decide) v hb
mask_input "8168|5986310706507378352962293074805895248510699696029696|1724250584377957311201208067402620470465053552543793152"
def inputClause8183 : CNF.NClause := [(156,false),(161,true),(166,true),(171,true),(176,true),(180,true)]
theorem inputList8183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 4) (closed_mem 1 4) inputClause8183 (by decide) v hb
mask_input "8183|91343852333181432387730302044767688728495783936|1631366126631324440774826306083565729898462958715928576"
def inputClause8189 : CNF.NClause := [(175,false),(176,true),(177,true),(178,true),(179,true),(185,true)]
theorem inputList8189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) inputClause8189 (by decide) v hb
mask_input "8189|47890485652059026823698344598447161988085597568237568|50476571877270214272178055206763308735442219836922396672"
def inputClause8197 : CNF.NClause := [(157,true),(164,true),(166,true),(173,true),(175,false),(182,true)]
theorem inputList8197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 7) (closed_mem 1 7) inputClause8197 (by decide) v hb
mask_input "8197|47890485652059026823698344598447161988085597568237568|6142071887695261328735633764998069917148927819721474048"
def inputClause8213 : CNF.NClause := [(156,false),(162,true),(168,true),(174,true),(175,true),(181,true)]
theorem inputList8213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 9) (closed_mem 1 9) inputClause8213 (by decide) v hb
mask_input "8213|91343852333181432387730302044767688728495783936|3137206800635572291710974529254795343804717183180734464"
def inputClause8218 : CNF.NClause := [(165,true),(166,false),(167,true),(168,true),(169,true),(185,true)]
theorem inputList8218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) inputClause8218 (by decide) v hb
mask_input "8218|93536104789177786765035829293842113257979682750464|49041213581227886545375197888334654586441892615275151360"
def inputClause8219 : CNF.NClause := [(165,false),(166,true),(167,true),(168,true),(169,true),(185,true)]
theorem inputList8219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) inputClause8219 (by decide) v hb
mask_input "8219|46768052394588893382517914646921056628989841375232|49041260349280281134268580406249301507498521605116526592"
def inputClause8227 : CNF.NClause := [(157,true),(161,true),(165,true),(174,true),(178,false),(184,true)]
theorem inputList8227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 12) (closed_mem 1 12) inputClause8227 (by decide) v hb
mask_input "8227|383123885216472214589586756787577295904684780545900544|24543923770423625164207485307449086962051914512419782656"
def inputClause8258 : CNF.NClause := [(157,true),(163,true),(169,true),(170,false),(176,true),(181,true)]
theorem inputList8258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 17) (closed_mem 1 17) inputClause8258 (by decide) v hb
mask_input "8258|1496577676626844588240573268701473812127674924007424|3161532216575012506244421435071129247919247981417594880"
def inputClause8279 : CNF.NClause := [(160,false),(161,true),(162,true),(163,true),(164,true),(185,true)]
theorem inputList8279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 20) (closed_mem 1 20) inputClause8279 (by decide) v hb
mask_input "8279|1461501637330902918203684832716283019655932542976|49039901152757563394554650979354875364290241587851558912"
def inputClause8281 : CNF.NClause := [(159,true),(160,true),(166,true),(172,true),(178,false),(181,true)]
theorem inputList8281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) inputClause8281 (by decide) v hb
mask_input "8281|383123885216472214589586756787577295904684780545900544|3071073120795530269210798688731967179023776407644798976"
def inputClause8282 : CNF.NClause := [(159,true),(160,true),(166,true),(172,false),(178,true),(181,true)]
theorem inputList8282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) inputClause8282 (by decide) v hb
mask_input "8282|5986310706507378352962293074805895248510699696029696|3448210695305495105447423152444738579679950488494669824"
def inputClause8286 : CNF.NClause := [(157,true),(160,true),(168,true),(171,true),(179,true),(183,false)]
theorem inputList8286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 22) (closed_mem 1 22) inputClause8286 (by decide) v hb
mask_input "8286|12259964326927110866866776217202473468949912977468817408|769616714394696826768497782575169713705053942594928640"
def inputClause8290 : CNF.NClause := [(157,true),(160,false),(168,true),(171,true),(179,true),(183,true)]
theorem inputList8290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 22) (closed_mem 1 22) inputClause8290 (by decide) v hb
mask_input "8290|1461501637330902918203684832716283019655932542976|13029579579820170362732355796092810466371947264131203072"
def inputClause8310 : CNF.NClause := [(155,true),(164,true),(168,true),(172,true),(176,true),(184,false)]
theorem inputList8310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) inputClause8310 (by decide) v hb
mask_input "8310|24519928653854221733733552434404946937899825954937634816|102164856127905604184826578411350070589872672732086272"
def inputClause8311 : CNF.NClause := [(155,true),(164,true),(168,true),(172,true),(176,false),(184,true)]
theorem inputList8311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) inputClause8311 (by decide) v hb
mask_input "8311|95780971304118053647396689196894323976171195136475136|24526312538678009284270982323619402684513527432533245952"
def inputClause8317 : CNF.NClause := [(155,true),(162,true),(169,true),(171,true),(178,false),(182,true)]
theorem inputList8317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) inputClause8317 (by decide) v hb
mask_input "8317|383123885216472214589586756787577295904684780545900544|6133729499333598035106378550377472306521198664022491136"
def inputClause8322 : CNF.NClause := [(155,true),(163,true),(166,true),(174,true),(177,true),(183,false)]
theorem inputList8322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) inputClause8322 (by decide) v hb
mask_input "8322|12259964326927110866866776217202473468949912977468817408|215612459224079612307469409866118823707644780448055296"
def inputClause8325 : CNF.NClause := [(155,true),(163,true),(166,false),(174,true),(177,true),(183,true)]
theorem inputList8325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) inputClause8325 (by decide) v hb
mask_input "8325|93536104789177786765035829293842113257979682750464|12475483250046401301387480591239298450544299778234122240"
def inputClause8332 : CNF.NClause := [(155,true),(161,false),(167,true),(173,true),(179,true),(181,true)]
theorem inputList8332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) inputClause8332 (by decide) v hb
mask_input "8332|2923003274661805836407369665432566039311865085952|3843398591459241424766038419549123456154229528464457728"
def inputClause8335 : CNF.NClause := [(155,true),(160,true),(165,true),(170,true),(175,false),(180,true)]
theorem inputList8335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 30) (closed_mem 1 30) inputClause8335 (by decide) v hb
mask_input "8335|47890485652059026823698344598447161988085597568237568|1534040393768473789333604515883641317154359807129419776"
def inputClause8343 : CNF.NClause := [(211,true),(212,true),(213,false),(214,true),(215,true),(216,true)]
theorem inputList8343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 0) (closed_mem 2 0) inputClause8343 (by decide) v hb
mask_input "8343|13164036458569648337239753460458804039861886925068638906788872192|194169537763902312974286363541767359587962832144762423875135864832"
def inputClause8351 : CNF.NClause := [(190,false),(195,true),(200,true),(205,true),(210,true),(211,true)]
theorem inputList8351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 1) (closed_mem 2 1) inputClause8351 (by decide) v hb
mask_input "8351|1569275433846670190958947355801916604025588861116008628224|4989592844238047899003902983034695542162769114539127465886875648"
def inputClause8366 : CNF.NClause := [(187,true),(192,true),(197,true),(202,false),(207,true),(211,true)]
theorem inputList8366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) inputClause8366 (by decide) v hb
mask_input "8366|6427752177035961102167848369364650410088811975131171341205504|3496904524824259830878289963853755151319620595399632162255798272"
def inputClause8369 : CNF.NClause := [(187,false),(192,true),(197,true),(202,true),(207,true),(211,true)]
theorem inputList8369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) inputClause8369 (by decide) v hb
mask_input "8369|196159429230833773869868419475239575503198607639501078528|3503332080841866561146683942354700326490133904176155694095925248"
def inputClause8371 : CNF.NClause := [(206,true),(207,true),(208,true),(209,true),(210,false),(216,true)]
theorem inputList8371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) inputClause8371 (by decide) v hb
mask_input "8371|1645504557321206042154969182557350504982735865633579863348609024|106854952191045817362438311292317948417316410274580592376200298496"
def inputClause8387 : CNF.NClause := [(188,false),(195,true),(197,true),(204,true),(206,true),(213,true)]
theorem inputList8387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 7) (closed_mem 2 7) inputClause8387 (by decide) v hb
mask_input "8387|392318858461667547739736838950479151006397215279002157056|13292842586179783026513663859423025354720307258789040894993498112"
def inputClause8395 : CNF.NClause := [(187,true),(193,true),(199,true),(205,true),(206,false),(212,true)]
theorem inputList8395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 9) (closed_mem 2 9) inputClause8395 (by decide) v hb
mask_input "8395|102844034832575377634685573909834406561420991602098741459288064|6634256466086141356770292039677755695085322767741756788111835136"
end Percolation.MaskChain
