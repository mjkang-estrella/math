import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8002 : CNF.NClause := [(144,true),(145,false),(146,true),(147,true),(148,true),(154,true)]
theorem inputList8002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) inputClause8002 (by decide) v hb
mask_input "8002|44601490397061246283071436545296723011960832|23482684694052746168037111341098724665797378048"
def inputClause8003 : CNF.NClause := [(144,false),(145,true),(146,true),(147,true),(148,true),(154,true)]
theorem inputList8003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) inputClause8003 (by decide) v hb
mask_input "8003|22300745198530623141535718272648361505980416|23504985439251276791178647059371373027303358464"
def inputClause8008 : CNF.NClause := [(128,true),(132,false),(136,true),(140,true),(144,true),(153,true)]
theorem inputList8008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) inputClause8008 (by decide) v hb
mask_input "8008|5444517870735015415413993718908291383296|11441763535989416516739279543534759939592421376"
def inputClause8012 : CNF.NClause := [(126,true),(133,true),(135,true),(142,false),(144,true),(151,true)]
theorem inputList8012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) inputClause8012 (by decide) v hb
mask_input "8012|5575186299632655785383929568162090376495104|2876850660859749465646877662952479575127359488"
def inputClause8014 : CNF.NClause := [(126,true),(133,false),(135,true),(142,true),(144,true),(151,true)]
theorem inputList8014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) inputClause8014 (by decide) v hb
mask_input "8014|10889035741470030830827987437816582766592|2882414958123640651401430764533203848921088000"
def inputClause8019 : CNF.NClause := [(127,true),(130,true),(138,false),(141,true),(144,true),(152,true)]
theorem inputList8019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) inputClause8019 (by decide) v hb
mask_input "8019|348449143727040986586495598010130648530944|5734080640442837619490457146040443395182166016"
def inputClause8025 : CNF.NClause := [(125,true),(131,true),(137,false),(143,true),(144,true),(150,true)]
theorem inputList8025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) inputClause8025 (by decide) v hb
mask_input "8025|174224571863520493293247799005065324265472|1460701575297987048395605186777153061758435328"
def inputClause8029 : CNF.NClause := [(134,true),(135,true),(136,true),(137,true),(138,false),(154,true)]
theorem inputList8029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) inputClause8029 (by decide) v hb
mask_input "8029|348449143727040986586495598010130648530944|22836289754367602197857500350815056679606943744"
def inputClause8030 : CNF.NClause := [(134,true),(135,true),(136,true),(137,false),(138,true),(154,true)]
theorem inputList8030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) inputClause8030 (by decide) v hb
mask_input "8030|174224571863520493293247799005065324265472|22836463978939465718350793598614061744931209216"
def inputClause8031 : CNF.NClause := [(134,true),(135,true),(136,false),(137,true),(138,true),(154,true)]
theorem inputList8031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) inputClause8031 (by decide) v hb
mask_input "8031|87112285931760246646623899502532662132736|22836551091225397478597440222513564277593341952"
def inputClause8032 : CNF.NClause := [(134,true),(135,false),(136,true),(137,true),(138,true),(154,true)]
theorem inputList8032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) inputClause8032 (by decide) v hb
mask_input "8032|43556142965880123323311949751266331066368|22836594647368363358720763534463315543924408320"
def inputClause8033 : CNF.NClause := [(134,false),(135,true),(136,true),(137,true),(138,true),(154,true)]
theorem inputList8033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 10) (closed_mem 0 10) inputClause8033 (by decide) v hb
mask_input "8033|21778071482940061661655974875633165533184|22836616425439846298782425190438191177089941504"
def inputClause8039 : CNF.NClause := [(128,false),(131,true),(134,true),(142,true),(145,true),(152,true)]
theorem inputList8039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) inputClause8039 (by decide) v hb
mask_input "8039|340282366920938463463374607431768211456|5759191947850951733870968606883174446230667264"
def inputClause8044 : CNF.NClause := [(126,true),(130,false),(134,true),(143,true),(147,true),(153,true)]
theorem inputList8044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) inputClause8044 (by decide) v hb
mask_input "8044|1361129467683753853853498429727072845824|11607559738977264015465618882731999654970392576"
def inputClause8047 : CNF.NClause := [(127,true),(133,true),(134,true),(140,true),(146,false),(150,true)]
theorem inputList8047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) inputClause8047 (by decide) v hb
mask_input "8047|89202980794122492566142873090593446023921664|1428674326529275915566356167491152824609275904"
def inputClause8048 : CNF.NClause := [(127,true),(133,true),(134,true),(140,false),(146,true),(150,true)]
theorem inputList8048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) inputClause8048 (by decide) v hb
mask_input "8048|1393796574908163946345982392040522594123776|1516483510748490244186153058189705748039073792"
def inputClause8050 : CNF.NClause := [(127,true),(133,false),(134,true),(140,true),(146,true),(150,true)]
theorem inputList8050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) inputClause8050 (by decide) v hb
mask_input "8050|10889035741470030830827987437816582766592|1517866418287656938101668212594308454050430976"
def inputClause8053 : CNF.NClause := [(125,true),(132,true),(134,true),(141,true),(148,false),(151,true)]
theorem inputList8053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) inputClause8053 (by decide) v hb
mask_input "8053|356811923176489970264571492362373784095686656|2857310243686385630203648906573491788381683712"
def inputClause8056 : CNF.NClause := [(125,true),(132,false),(134,true),(141,true),(148,true),(151,true)]
theorem inputList8056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) inputClause8056 (by decide) v hb
mask_input "8056|5444517870735015415413993718908291383296|3214116722345004865452804984942146664185987072"
def inputClause8057 : CNF.NClause := [(125,false),(132,true),(134,true),(141,true),(148,true),(151,true)]
theorem inputList8057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) inputClause8057 (by decide) v hb
mask_input "8057|42535295865117307932921825928971026432|3214122124327579735350912466014039643506343936"
def inputClause8059 : CNF.NClause := [(139,true),(140,true),(141,true),(142,true),(143,false),(154,true)]
theorem inputList8059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) inputClause8059 (by decide) v hb
mask_input "8059|11150372599265311570767859136324180752990208|22846416557607169326530170379132226101579874304"
def inputClause8060 : CNF.NClause := [(139,true),(140,true),(141,true),(142,false),(143,true),(154,true)]
theorem inputList8060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) inputClause8060 (by decide) v hb
mask_input "8060|5575186299632655785383929568162090376495104|22851991743906801982315554308700388191956369408"
def inputClause8061 : CNF.NClause := [(139,true),(140,true),(141,false),(142,true),(143,true),(154,true)]
theorem inputList8061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) inputClause8061 (by decide) v hb
mask_input "8061|2787593149816327892691964784081045188247552|22854779337056618310208246273484469237144616960"
def inputClause8062 : CNF.NClause := [(139,true),(140,false),(141,true),(142,true),(143,true),(154,true)]
theorem inputList8062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) inputClause8062 (by decide) v hb
mask_input "8062|1393796574908163946345982392040522594123776|22856173133631526474154592255876509759738740736"
def inputClause8063 : CNF.NClause := [(139,false),(140,true),(141,true),(142,true),(143,true),(154,true)]
theorem inputList8063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 15) (closed_mem 0 15) inputClause8063 (by decide) v hb
mask_input "8063|696898287454081973172991196020261297061888|22856870031918980556127765247072530021035802624"
def inputClause8069 : CNF.NClause := [(128,false),(130,true),(137,true),(139,true),(146,true),(151,true)]
theorem inputList8069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 16) (closed_mem 0 16) inputClause8069 (by decide) v hb
mask_input "8069|340282366920938463463374607431768211456|2944570850194827540903034904483038772483588096"
def inputClause8072 : CNF.NClause := [(126,true),(132,true),(138,true),(139,false),(145,true),(150,true)]
theorem inputList8072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 17) (closed_mem 0 17) inputClause8072 (by decide) v hb
mask_input "8072|696898287454081973172991196020261297061888|1472203161835210633577975181430172756276674560"
def inputClause8078 : CNF.NClause := [(127,true),(131,true),(135,true),(139,false),(148,true),(153,true)]
theorem inputList8078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) inputClause8078 (by decide) v hb
mask_input "8078|696898287454081973172991196020261297061888|11774839913367253726831121998592249311518523392"
def inputClause8079 : CNF.NClause := [(127,true),(131,true),(135,false),(139,true),(148,true),(153,true)]
theorem inputList8079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 18) (closed_mem 0 18) inputClause8079 (by decide) v hb
mask_input "8079|43556142965880123323311949751266331066368|11775493255511741928680971677838518306484518912"
def inputClause8089 : CNF.NClause := [(129,true),(130,true),(131,true),(132,true),(133,false),(154,true)]
theorem inputList8089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) inputClause8089 (by decide) v hb
mask_input "8089|10889035741470030830827987437816582766592|22835973291766365725086479412430145135170289664"
def inputClause8090 : CNF.NClause := [(129,true),(130,true),(131,true),(132,false),(133,true),(154,true)]
theorem inputList8090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) inputClause8090 (by decide) v hb
mask_input "8090|5444517870735015415413993718908291383296|22835978736284236460101894826423864043461672960"
def inputClause8091 : CNF.NClause := [(129,true),(130,true),(131,false),(132,true),(133,true),(154,true)]
theorem inputList8091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) inputClause8091 (by decide) v hb
mask_input "8091|2722258935367507707706996859454145691648|22835981458543171827609602533420723497607364608"
def inputClause8092 : CNF.NClause := [(129,true),(130,false),(131,true),(132,true),(133,true),(154,true)]
theorem inputList8092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) inputClause8092 (by decide) v hb
mask_input "8092|1361129467683753853853498429727072845824|22835982819672639511363456386919153224680210432"
def inputClause8093 : CNF.NClause := [(129,false),(130,true),(131,true),(132,true),(133,true),(154,true)]
theorem inputList8093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 20) (closed_mem 0 20) inputClause8093 (by decide) v hb
mask_input "8093|680564733841876926926749214863536422912|22835983500237373353240383313668368088216633344"
def inputClause8099 : CNF.NClause := [(128,false),(129,true),(135,true),(141,true),(147,true),(150,true)]
theorem inputList8099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) inputClause8099 (by decide) v hb
mask_input "8099|340282366920938463463374607431768211456|1608485484151720916083513919113729203486326784"
def inputClause8100 : CNF.NClause := [(126,true),(129,true),(137,true),(140,true),(148,true),(152,false)]
theorem inputList8100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) inputClause8100 (by decide) v hb
mask_input "8100|5708990770823839524233143877797980545530986496|358380709958587226815753515146286093492551680"
def inputClause8102 : CNF.NClause := [(126,true),(129,true),(137,true),(140,false),(148,true),(152,true)]
theorem inputList8102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) inputClause8102 (by decide) v hb
mask_input "8102|1393796574908163946345982392040522594123776|6065977684207518587102551410552226116429414400"
def inputClause8103 : CNF.NClause := [(126,true),(129,true),(137,false),(140,true),(148,true),(152,true)]
theorem inputList8103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) inputClause8103 (by decide) v hb
mask_input "8103|174224571863520493293247799005065324265472|6067197256210563230555604145145261573699272704"
def inputClause8104 : CNF.NClause := [(126,true),(129,false),(137,true),(140,true),(148,true),(152,true)]
theorem inputList8104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 22) (closed_mem 0 22) inputClause8104 (by decide) v hb
mask_input "8104|680564733841876926926749214863536422912|6067370800217692909171970466195051775487115264"
def inputClause8107 : CNF.NClause := [(127,true),(129,true),(136,true),(143,true),(145,false),(151,true)]
theorem inputList8107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 23) (closed_mem 0 23) inputClause8107 (by decide) v hb
mask_input "8107|44601490397061246283071436545296723011960832|2865733721003034136280145080371335565601144832"
end Percolation.MaskChain
