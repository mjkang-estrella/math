import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7955 : CNF.NClause := [(49,false),(96,false),(100,false),(104,false),(108,false),(117,false),(122,false)]
theorem inputList7955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 18) (final_mem 18) inputClause7955 (by decide) v hb
mask_input "7955|5483411630454802796619713267128860672|0"
def inputClause7956 : CNF.NClause := [(50,false),(94,false),(102,false),(105,false),(108,false),(116,false),(121,false)]
theorem inputList7956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 19) (final_mem 19) inputClause7956 (by decide) v hb
mask_input "7956|2741902915088696259416549397457010688|0"
def inputClause7957 : CNF.NClause := [(51,false),(98,false),(99,false),(100,false),(101,false),(102,false),(123,false)]
theorem inputList7957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 20) (final_mem 20) inputClause7957 (by decide) v hb
mask_input "7957|10633833790571478752010569881506283520|0"
def inputClause7958 : CNF.NClause := [(52,false),(97,false),(98,false),(104,false),(110,false),(116,false),(119,false)]
theorem inputList7958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 21) (final_mem 21) inputClause7958 (by decide) v hb
mask_input "7958|749009579622227622676477203632357376|0"
def inputClause7959 : CNF.NClause := [(53,false),(95,false),(98,false),(106,false),(109,false),(117,false),(121,false)]
theorem inputList7959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 22) (final_mem 22) inputClause7959 (by decide) v hb
mask_input "7959|2825340014315409004254378474344546304|0"
def inputClause7960 : CNF.NClause := [(54,false),(96,false),(98,false),(105,false),(112,false),(114,false),(120,false)]
theorem inputList7960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 23) (final_mem 23) inputClause7960 (by decide) v hb
mask_input "7960|1355230441037609885727009802658250752|0"
def inputClause7961 : CNF.NClause := [(55,false),(94,false),(98,false),(107,false),(111,false),(115,false),(122,false)]
theorem inputList7961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 24) (final_mem 24) inputClause7961 (by decide) v hb
mask_input "7961|5361209102433729425480592607510790144|0"
def inputClause7963 : CNF.NClause := [(57,false),(93,false),(102,false),(106,false),(110,false),(114,false),(122,false)]
theorem inputList7963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 26) (final_mem 26) inputClause7963 (by decide) v hb
mask_input "7963|5339065454932772343062942013607378944|0"
def inputClause7964 : CNF.NClause := [(58,false),(93,false),(100,false),(107,false),(109,false),(116,false),(120,false)]
theorem inputList7964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 27) (final_mem 27) inputClause7964 (by decide) v hb
mask_input "7964|1413117319459739724577926963647217664|0"
def inputClause7965 : CNF.NClause := [(59,false),(93,false),(101,false),(104,false),(112,false),(115,false),(121,false)]
theorem inputList7965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 28) (final_mem 28) inputClause7965 (by decide) v hb
mask_input "7965|2705209490910969617453118479677784064|0"
def inputClause7966 : CNF.NClause := [(60,false),(93,false),(99,false),(105,false),(111,false),(117,false),(119,false)]
theorem inputList7966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 29) (final_mem 29) inputClause7966 (by decide) v hb
mask_input "7966|833404854342867567270657007493840896|0"
def inputClause8004 : CNF.NClause := [(128,true),(132,true),(136,true),(140,true),(144,true),(153,false)]
theorem inputList8004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) inputClause8004 (by decide) v hb
mask_input "8004|11417981541647679048466287755595961091061972992|23787438859608203288407201932517756821831680"
def inputClause8005 : CNF.NClause := [(128,true),(132,true),(136,true),(140,true),(144,false),(153,true)]
theorem inputList8005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) inputClause8005 (by decide) v hb
mask_input "8005|22300745198530623141535718272648361505980416|11419468235308756628613159239255830486377824256"
def inputClause8006 : CNF.NClause := [(128,true),(132,true),(136,true),(140,false),(144,true),(153,true)]
theorem inputList8006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) inputClause8006 (by decide) v hb
mask_input "8006|1393796574908163946345982392040522594123776|11440375183932379087808348975136438325289680896"
def inputClause8007 : CNF.NClause := [(128,true),(132,true),(136,false),(140,true),(144,true),(153,true)]
theorem inputList8007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) inputClause8007 (by decide) v hb
mask_input "8007|87112285931760246646623899502532662132736|11441681868221355491508048333628976315221671936"
def inputClause8009 : CNF.NClause := [(128,false),(132,true),(136,true),(140,true),(144,true),(153,true)]
theorem inputList8009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) inputClause8009 (by decide) v hb
mask_input "8009|340282366920938463463374607431768211456|11441768640224920330816231494153871416115593216"
def inputClause8010 : CNF.NClause := [(126,true),(133,true),(135,true),(142,true),(144,true),(151,false)]
theorem inputList8010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) inputClause8010 (by decide) v hb
mask_input "8010|2854495385411919762116571938898990272765493248|27930461747462359315689653621651392738361344"
def inputClause8011 : CNF.NClause := [(126,true),(133,true),(135,true),(142,true),(144,false),(151,true)]
theorem inputList8011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) inputClause8011 (by decide) v hb
mask_input "8011|22300745198530623141535718272648361505980416|2860125101960851498290725874247993303997874176"
def inputClause8013 : CNF.NClause := [(126,true),(133,true),(135,false),(142,true),(144,true),(151,true)]
theorem inputList8013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) inputClause8013 (by decide) v hb
mask_input "8013|43556142965880123323311949751266331066368|2882382291016416241308938280570890399172788224"
def inputClause8015 : CNF.NClause := [(126,false),(133,true),(135,true),(142,true),(144,true),(151,true)]
theorem inputList8015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) inputClause8015 (by decide) v hb
mask_input "8015|85070591730234615865843651857942052864|2882425762088790391197645726676989807561801728"
def inputClause8016 : CNF.NClause := [(127,true),(130,true),(138,true),(141,true),(144,true),(152,false)]
theorem inputList8016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) inputClause8016 (by decide) v hb
mask_input "8016|5708990770823839524233143877797980545530986496|25438318762725136243899763840472980299710464"
def inputClause8017 : CNF.NClause := [(127,true),(130,true),(138,true),(141,true),(144,false),(152,true)]
theorem inputList8017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) inputClause8017 (by decide) v hb
mask_input "8017|22300745198530623141535718272648361505980416|5712128344388034037335507923365805164324716544"
def inputClause8018 : CNF.NClause := [(127,true),(130,true),(138,true),(141,false),(144,true),(152,true)]
theorem inputList8018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) inputClause8018 (by decide) v hb
mask_input "8018|2787593149816327892691964784081045188247552|5731641496436748332584351676854372480642449408"
def inputClause8020 : CNF.NClause := [(127,true),(130,false),(138,true),(141,true),(144,true),(152,true)]
theorem inputList8020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) inputClause8020 (by decide) v hb
mask_input "8020|1361129467683753853853498429727072845824|5734427728457096976723189788140023798757851136"
def inputClause8022 : CNF.NClause := [(125,true),(131,true),(137,true),(143,true),(144,true),(150,false)]
theorem inputList8022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) inputClause8022 (by decide) v hb
mask_input "8022|1427247692705959881058285969449495136382746624|33628107163890687830612465126662990699954176"
def inputClause8023 : CNF.NClause := [(125,true),(131,true),(137,true),(143,true),(144,false),(150,true)]
theorem inputList8023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) inputClause8023 (by decide) v hb
mask_input "8023|22300745198530623141535718272648361505980416|1438575054671319945747362716303509765576720384"
def inputClause8024 : CNF.NClause := [(125,true),(131,true),(137,true),(143,false),(144,true),(150,true)]
theorem inputList8024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) inputClause8024 (by decide) v hb
mask_input "8024|11150372599265311570767859136324180752990208|1449725427270585257318130575439833946329710592"
def inputClause8026 : CNF.NClause := [(125,true),(131,false),(137,true),(143,true),(144,true),(150,true)]
theorem inputList8026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) inputClause8026 (by decide) v hb
mask_input "8026|2722258935367507707706996859454145691648|1460873077610915201381190727579298672937009152"
def inputClause8027 : CNF.NClause := [(125,false),(131,true),(137,true),(143,true),(144,true),(150,true)]
theorem inputList8027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) inputClause8027 (by decide) v hb
mask_input "8027|42535295865117307932921825928971026432|1460875757334554703771590501654332198111674368"
def inputClause8034 : CNF.NClause := [(128,true),(131,true),(134,true),(142,true),(145,true),(152,false)]
theorem inputList8034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) inputClause8034 (by decide) v hb
mask_input "8034|5708990770823839524233143877797980545530986496|50201517309479130576288192459801332467892224"
def inputClause8035 : CNF.NClause := [(128,true),(131,true),(134,true),(142,true),(145,false),(152,true)]
theorem inputList8035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) inputClause8035 (by decide) v hb
mask_input "8035|44601490397061246283071436545296723011960832|5714590797736257408526360633712485154986917888"
def inputClause8036 : CNF.NClause := [(128,true),(131,true),(134,true),(142,false),(145,true),(152,true)]
theorem inputList8036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) inputClause8036 (by decide) v hb
mask_input "8036|5575186299632655785383929568162090376495104|5753617101833685999024048140689619787622383616"
def inputClause8037 : CNF.NClause := [(128,true),(131,true),(134,false),(142,true),(145,true),(152,true)]
theorem inputList8037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) inputClause8037 (by decide) v hb
mask_input "8037|21778071482940061661655974875633165533184|5759170510061835714747770414282906244833345536"
def inputClause8038 : CNF.NClause := [(128,true),(131,false),(134,true),(142,true),(145,true),(152,true)]
theorem inputList8038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 11) (closed_mem 0 11) inputClause8038 (by decide) v hb
mask_input "8038|2722258935367507707706996859454145691648|5759189565874383287301724363260922423853187072"
def inputClause8040 : CNF.NClause := [(126,true),(130,true),(134,true),(143,true),(147,true),(153,false)]
theorem inputList8040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) inputClause8040 (by decide) v hb
mask_input "8040|11417981541647679048466287755595961091061972992|189579558459052650753184980634468290981265408"
def inputClause8043 : CNF.NClause := [(126,true),(130,true),(134,false),(143,true),(147,true),(153,true)]
theorem inputList8043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) inputClause8043 (by decide) v hb
mask_input "8043|21778071482940061661655974875633165533184|11607539322035248759157811080255553748877705216"
def inputClause8045 : CNF.NClause := [(126,false),(130,true),(134,true),(143,true),(147,true),(153,true)]
theorem inputList8045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 12) (closed_mem 0 12) inputClause8045 (by decide) v hb
mask_input "8045|85070591730234615865843651857942052864|11607561015036139968984856870386777524101185536"
def inputClause8046 : CNF.NClause := [(127,true),(133,true),(134,true),(140,true),(146,true),(150,false)]
theorem inputList8046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) inputClause8046 (by decide) v hb
mask_input "8046|1427247692705959881058285969449495136382746624|90629614617438527074213071132251134250450944"
def inputClause8049 : CNF.NClause := [(127,true),(133,true),(134,false),(140,true),(146,true),(150,true)]
theorem inputList8049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 13) (closed_mem 0 13) inputClause8049 (by decide) v hb
mask_input "8049|21778071482940061661655974875633165533184|1517855529251915468070837384606870637467664384"
def inputClause8054 : CNF.NClause := [(125,true),(132,true),(134,true),(141,false),(148,true),(151,true)]
theorem inputList8054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) inputClause8054 (by decide) v hb
mask_input "8054|2787593149816327892691964784081045188247552|3211334573713059272575528434151784527289122816"
end Percolation.MaskChain
