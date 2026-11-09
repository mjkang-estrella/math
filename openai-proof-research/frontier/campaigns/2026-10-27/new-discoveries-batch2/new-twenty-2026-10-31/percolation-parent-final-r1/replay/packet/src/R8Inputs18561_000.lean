import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1120 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,true),(21,true),(26,false)]
theorem inputList1120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1120 (by decide) v hb
mask_input "1120|604462909807314654461952|2146564"
def inputClause1136 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,true),(21,false),(26,true)]
theorem inputList1136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1136 (by decide) v hb
mask_input "1136|604462909807314589450240|67158276"
def inputClause1148 : CNF.NClause := [(79,false),(2,true),(8,true),(14,false),(15,true),(21,true),(26,true)]
theorem inputList1148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1148 (by decide) v hb
mask_input "1148|604462909807314587369472|69239044"
def inputClause1150 : CNF.NClause := [(79,false),(2,true),(8,false),(14,true),(15,true),(21,true),(26,true)]
theorem inputList1150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1150 (by decide) v hb
mask_input "1150|604462909807314587353344|69255172"
def inputClause1151 : CNF.NClause := [(79,false),(2,false),(8,true),(14,true),(15,true),(21,true),(26,true)]
theorem inputList1151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1151 (by decide) v hb
mask_input "1151|604462909807314587353092|69255424"
def inputClause1598 : CNF.NClause := [(86,false),(1,true),(5,false),(14,true),(18,true),(22,true),(29,true)]
theorem inputList1598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1598 (by decide) v hb
mask_input "1598|77371252455336267181195296|541343746"
def inputClause8155 : CNF.NClause := [(180,true),(181,true),(182,true),(183,true),(184,false),(185,true)]
theorem inputList8155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) inputClause8155 (by decide) v hb
mask_input "8155|24519928653854221733733552434404946937899825954937634816|72027290420696776342842310276064531630080738742629302272"
def inputClause8156 : CNF.NClause := [(180,true),(181,true),(182,true),(183,false),(184,true),(185,true)]
theorem inputList8156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) inputClause8156 (by decide) v hb
mask_input "8156|12259964326927110866866776217202473468949912977468817408|84287254747623887209709086493267005099030651720098119680"
def inputClause8158 : CNF.NClause := [(180,true),(181,false),(182,true),(183,true),(184,true),(185,true)]
theorem inputList8158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 0) (closed_mem 1 0) inputClause8158 (by decide) v hb
mask_input "8158|3064991081731777716716694054300618367237478244367204352|93482227992819220359859168656168860200743086453199732736"
def inputClause8161 : CNF.NClause := [(159,true),(164,true),(169,true),(174,true),(179,false),(180,true)]
theorem inputList8161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) inputClause8161 (by decide) v hb
mask_input "8161|766247770432944429179173513575154591809369561091801088|1557213187307247753962466846883623320188670081316683776"
def inputClause8162 : CNF.NClause := [(159,true),(164,true),(169,true),(174,false),(179,true),(180,true)]
theorem inputList8162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) inputClause8162 (by decide) v hb
mask_input "8162|23945242826029513411849172299223580994042798784118784|2299515714914162669729791188159554331003996843624366080"
def inputClause8163 : CNF.NClause := [(159,true),(164,true),(169,false),(174,true),(179,true),(180,true)]
theorem inputList8163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) inputClause8163 (by decide) v hb
mask_input "8163|748288838313422294120286634350736906063837462003712|2322712668901878760847520073824427175091975804946481152"
def inputClause8167 : CNF.NClause := [(157,true),(162,true),(167,true),(172,true),(177,false),(180,true)]
theorem inputList8167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) inputClause8167 (by decide) v hb
mask_input "8167|191561942608236107294793378393788647952342390272950272|1538674952476228582259376982083637717761221861966872576"
def inputClause8169 : CNF.NClause := [(157,true),(162,true),(167,false),(172,true),(177,true),(180,true)]
theorem inputList8169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) inputClause8169 (by decide) v hb
mask_input "8169|187072209578355573530071658587684226515959365500928|1730049822874886333980640288818838681487048292874321920"
def inputClause8171 : CNF.NClause := [(157,false),(162,true),(167,true),(172,true),(177,true),(180,true)]
theorem inputList8171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) inputClause8171 (by decide) v hb
mask_input "8171|182687704666362864775460604089535377456991567872|1730236712396760023191305585016822276178186795248254976"
def inputClause8175 : CNF.NClause := [(158,true),(163,true),(168,false),(173,true),(178,true),(180,true)]
theorem inputList8175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 3) (closed_mem 1 3) inputClause8175 (by decide) v hb
mask_input "8175|374144419156711147060143317175368453031918731001856|1927604104883883809602933550487368179355357463565041664"
def inputClause8176 : CNF.NClause := [(158,true),(163,false),(168,true),(173,true),(178,true),(180,true)]
theorem inputList8176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 3) (closed_mem 1 3) inputClause8176 (by decide) v hb
mask_input "8176|11692013098647223345629478661730264157247460343808|1927966557289941873526648064325881817544232134835699712"
def inputClause8177 : CNF.NClause := [(158,false),(163,true),(168,true),(173,true),(178,true),(180,true)]
theorem inputList8177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 3) (closed_mem 1 3) inputClause8177 (by decide) v hb
mask_input "8177|365375409332725729550921208179070754913983135744|1927977883927631188024264142883335368737634468312907776"
def inputClause8185 : CNF.NClause := [(175,true),(176,true),(177,true),(178,true),(179,false),(185,true)]
theorem inputList8185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) inputClause8185 (by decide) v hb
mask_input "8185|766247770432944429179173513575154591809369561091801088|49758214592489328869822580037786601305620935873398833152"
def inputClause8186 : CNF.NClause := [(175,true),(176,true),(177,true),(178,false),(179,true),(185,true)]
theorem inputList8186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) inputClause8186 (by decide) v hb
mask_input "8186|383123885216472214589586756787577295904684780545900544|50141338477705801084412166794574178601525620653944733696"
def inputClause8188 : CNF.NClause := [(175,true),(176,false),(177,true),(178,true),(179,true),(185,true)]
theorem inputList8188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) inputClause8188 (by decide) v hb
mask_input "8188|95780971304118053647396689196894323976171195136475136|50428681391618155245354356862164861573454134239354159104"
def inputClause8190 : CNF.NClause := [(159,true),(163,true),(167,true),(171,true),(175,true),(184,false)]
theorem inputList8190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 6) (closed_mem 1 6) inputClause8190 (by decide) v hb
mask_input "8190|24519928653854221733733552434404946937899825954937634816|51083135978808384248514294115515882244523982208368640"
def inputClause8191 : CNF.NClause := [(159,true),(163,true),(167,true),(171,true),(175,false),(184,true)]
theorem inputList8191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 6) (closed_mem 1 6) inputClause8191 (by decide) v hb
mask_input "8191|47890485652059026823698344598447161988085597568237568|24523121304180971091158368383922015658156264339577765888"
def inputClause8194 : CNF.NClause := [(159,true),(163,false),(167,true),(171,true),(175,true),(184,true)]
theorem inputList8194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 6) (closed_mem 1 6) inputClause8194 (by decide) v hb
mask_input "8194|11692013098647223345629478661730264157247460343808|24571000097819931470758721099041801089880192689685659648"
def inputClause8198 : CNF.NClause := [(157,true),(164,true),(166,true),(173,false),(175,true),(182,true)]
theorem inputList8198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 7) (closed_mem 1 7) inputClause8198 (by decide) v hb
mask_input "8198|11972621413014756705924586149611790497021399392059392|6177989751934305598853407523446905288639992017897652224"
def inputClause8199 : CNF.NClause := [(157,true),(164,true),(166,false),(173,true),(175,true),(182,true)]
theorem inputList8199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 7) (closed_mem 1 7) inputClause8199 (by decide) v hb
mask_input "8199|93536104789177786765035829293842113257979682750464|6189868837242531177772567073767223237023755437606961152"
def inputClause8204 : CNF.NClause := [(158,true),(161,true),(169,true),(172,false),(175,true),(183,true)]
theorem inputList8204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 8) (closed_mem 1 8) inputClause8204 (by decide) v hb
mask_input "8204|5986310706507378352962293074805895248510699696029696|12308606389796167310516160806726144979480856638347280384"
def inputClause8215 : CNF.NClause := [(165,true),(166,true),(167,true),(168,true),(169,false),(185,true)]
theorem inputList8215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) inputClause8215 (by decide) v hb
mask_input "8215|748288838313422294120286634350736906063837462003712|49040558828494362300867842637529597691649086757495898112"
def inputClause8216 : CNF.NClause := [(165,true),(166,true),(167,true),(168,false),(169,true),(185,true)]
theorem inputList8216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) inputClause8216 (by decide) v hb
mask_input "8216|374144419156711147060143317175368453031918731001856|49040932972913519012014902780846773060102118676226899968"
def inputClause8222 : CNF.NClause := [(159,true),(162,true),(165,true),(173,false),(176,true),(183,true)]
theorem inputList8222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 11) (closed_mem 1 11) inputClause8222 (by decide) v hb
mask_input "8222|11972621413014756705924586149611790497021399392059392|12355798643040991498470687340895761937256301614143111168"
def inputClause8225 : CNF.NClause := [(159,false),(162,true),(165,true),(173,true),(176,true),(183,true)]
theorem inputList8225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 11) (closed_mem 1 11) inputClause8225 (by decide) v hb
mask_input "8225|730750818665451459101842416358141509827966271488|12367770533703187589725152825202957369611813185568899072"
def inputClause8237 : CNF.NClause := [(158,false),(164,true),(165,true),(171,true),(177,true),(181,true)]
theorem inputList8237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 13) (closed_mem 1 13) inputClause8237 (by decide) v hb
mask_input "8237|365375409332725729550921208179070754913983135744|3259616331771859396528042356103780344399019469250232320"
def inputClause8243 : CNF.NClause := [(156,false),(163,true),(165,true),(172,true),(179,true),(182,true)]
theorem inputList8243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 14) (closed_mem 1 14) inputClause8243 (by decide) v hb
mask_input "8243|91343852333181432387730302044767688728495783936|6902274704668500477082252062644505872853622986823958528"
def inputClause8245 : CNF.NClause := [(170,true),(171,true),(172,true),(173,true),(174,false),(185,true)]
theorem inputList8245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 15) (closed_mem 1 15) inputClause8245 (by decide) v hb
mask_input "8245|23945242826029513411849172299223580994042798784118784|49062305972857846136290713467840415982981567033735380992"
def inputClause8248 : CNF.NClause := [(170,true),(171,false),(172,true),(173,true),(174,true),(185,true)]
theorem inputList8248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 15) (closed_mem 1 15) inputClause8248 (by decide) v hb
mask_input "8248|2993155353253689176481146537402947624255349848014848|49083258060330621960526081493602236616351354482671484928"
def inputClause8250 : CNF.NClause := [(159,true),(161,true),(168,true),(170,true),(177,true),(182,false)]
theorem inputList8250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) inputClause8250 (by decide) v hb
mask_input "8250|6129982163463555433433388108601236734474956488734408704|193436318458112990287389604191747280925051123759316992"
def inputClause8251 : CNF.NClause := [(159,true),(161,true),(168,true),(170,true),(177,false),(182,true)]
theorem inputList8251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) inputClause8251 (by decide) v hb
mask_input "8251|191561942608236107294793378393788647952342390272950272|6131856539313432316425984334399195367447665222220775424"
def inputClause8252 : CNF.NClause := [(159,true),(161,true),(168,true),(170,false),(177,true),(182,true)]
theorem inputList8252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) inputClause8252 (by decide) v hb
mask_input "8252|1496577676626844588240573268701473812127674924007424|6321921904245041579132537139524282541587879937569718272"
def inputClause8253 : CNF.NClause := [(159,true),(161,true),(168,false),(170,true),(177,true),(182,true)]
theorem inputList8253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) inputClause8253 (by decide) v hb
mask_input "8253|374144419156711147060143317175368453031918731001856|6323044337502511712573717569475808646946975693762723840"
def inputClause8255 : CNF.NClause := [(159,false),(161,true),(168,true),(170,true),(177,true),(182,true)]
theorem inputList8255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) inputClause8255 (by decide) v hb
mask_input "8255|730750818665451459101842416358141509827966271488|6323417751170849758269318610950567657258497784527454208"
end Percolation.MaskChain
