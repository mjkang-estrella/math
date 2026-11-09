import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9146 : CNF.NClause := [(320,true),(321,true),(322,true),(323,false),(324,true),(340,true)]
theorem inputList9146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) inputClause9146 (by decide) v hb
mask_input "9146|17087896287367280659160173649356416916821636178853222159576332862577757806245124400183696695492608|2239793869879630391489337366067686177820281359438663737913697882920771782233853900113528021399606657024"
def inputClause9147 : CNF.NClause := [(320,true),(321,true),(322,false),(323,true),(324,true),(340,true)]
theorem inputList9147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) inputClause9147 (by decide) v hb
mask_input "9147|8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304|2239802413827774075129666946154510856028739770256753164524777671087203071112757022675728113247954403328"
def inputClause9150 : CNF.NClause := [(314,true),(317,true),(320,true),(328,true),(331,true),(338,false)]
theorem inputList9150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) inputClause9150 (by decide) v hb
mask_input "9150|559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944|4923750490974624117900861832648247717425349929355541039023704708756316467573314370380274589432283136"
def inputClause9153 : CNF.NClause := [(314,true),(317,true),(320,false),(328,true),(331,true),(338,true)]
theorem inputList9153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) inputClause9153 (by decide) v hb
mask_input "9153|2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576|564857800048389755847179036953053147695722121533495568111251032908096462042887770075049624945247125504"
def inputClause9155 : CNF.NClause := [(314,false),(317,true),(320,true),(328,true),(331,true),(338,true)]
theorem inputList9155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) inputClause9155 (by decide) v hb
mask_input "9155|33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384|564859902660628240493041394552545158348584933570759762941321449527179162040430335393091053798551453696"
def inputClause9160 : CNF.NClause := [(312,true),(316,false),(320,true),(329,true),(333,true),(339,true)]
theorem inputList9160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 12) (closed_mem 6 12) inputClause9160 (by decide) v hb
mask_input "9160|133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536|1138466146580292986612024813591981629943252239151253970268058430283619638858546752509015780129782104064"
def inputClause9163 : CNF.NClause := [(313,true),(319,true),(320,true),(326,true),(332,false),(336,true)]
theorem inputList9163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) inputClause9163 (by decide) v hb
mask_input "9163|8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296|140123970224364300902347035168388952495735216057009037599030615246811908451890298703585644400561094656"
def inputClause9167 : CNF.NClause := [(313,false),(319,true),(320,true),(326,true),(332,true),(336,true)]
theorem inputList9167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) inputClause9167 (by decide) v hb
mask_input "9167|16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192|148872956436097630467727025365752358507521998446952806433383932461189159337596194735225400054262005760"
def inputClause9175 : CNF.NClause := [(325,true),(326,true),(327,true),(328,true),(329,false),(340,true)]
theorem inputList9175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) inputClause9175 (by decide) v hb
mask_input "9175|1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912|2240770015955046247396991890987405663136654795405380728229563680935546536648535652844888515073336672256"
def inputClause9177 : CNF.NClause := [(325,true),(326,true),(327,false),(328,true),(329,true),(340,true)]
theorem inputList9177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) inputClause9177 (by decide) v hb
mask_input "9177|273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728|2241590234976839876868631579322574771148662233941965682893223344912950269023235418816097332514720317440"
def inputClause9188 : CNF.NClause := [(312,true),(318,true),(324,true),(325,false),(331,true),(336,true)]
theorem inputList9188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) inputClause9188 (by decide) v hb
mask_input "9188|68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432|144393265968711860863479075448041805059984424054254856867287382054815289573248550172316891344629923840"
def inputClause9193 : CNF.NClause := [(313,true),(317,true),(321,true),(325,true),(334,false),(339,true)]
theorem inputList9193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) inputClause9193 (by decide) v hb
mask_input "9193|34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184|1119945278333901624467392889111052254476359461242779269137118758488025429949314344710462577271411572736"
def inputClause9198 : CNF.NClause := [(311,true),(319,true),(322,true),(325,true),(333,true),(338,false)]
theorem inputList9198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) inputClause9198 (by decide) v hb
mask_input "9198|559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944|17575973496924888146014940786992929437414827995618987545346673172780775291358902681177517795955441664"
def inputClause9214 : CNF.NClause := [(314,true),(315,false),(321,true),(327,true),(333,true),(336,true)]
theorem inputList9214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 21) (closed_mem 6 21) inputClause9214 (by decide) v hb
mask_input "9214|66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768|157759763873844013129751550596484938979578341279475822105448129493058626728889765066104527925744238592"
def inputClause9216 : CNF.NClause := [(312,true),(315,true),(323,true),(326,true),(334,true),(338,false)]
theorem inputList9216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) inputClause9216 (by decide) v hb
mask_input "9216|559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944|35149877756408727910387561396708007121218634621231942083322460149003972807358455366822200847389163520"
def inputClause9217 : CNF.NClause := [(312,true),(315,true),(323,true),(326,true),(334,false),(338,true)]
theorem inputList9217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) inputClause9217 (by decide) v hb
mask_input "9217|34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184|560090051704331589759788095904937134805979298035602926825507405687392692615208676940465363332922081280"
def inputClause9218 : CNF.NClause := [(312,true),(315,true),(323,true),(326,false),(334,true),(338,true)]
theorem inputList9218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) inputClause9218 (by decide) v hb
mask_input "9218|136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864|594949360130560842304474850149624225316295435840463500031043124727051318539948730716840104591727001600"
def inputClause9219 : CNF.NClause := [(312,true),(315,true),(323,false),(326,true),(334,true),(338,true)]
theorem inputList9219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) inputClause9219 (by decide) v hb
mask_input "9219|17087896287367280659160173649356416916821636178853222159576332862577757806245124400183696695492608|595068975404572413269088971365169720234713187293715472586160159057089362844592446587641390468595449856"
def inputClause9221 : CNF.NClause := [(312,false),(315,true),(323,true),(326,true),(334,true),(338,true)]
theorem inputList9221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) inputClause9221 (by decide) v hb
mask_input "9221|8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096|595086054957160421483693122183265536926817061263079785352644852784320660046852887881414425638095290368"
def inputClause9223 : CNF.NClause := [(313,true),(315,true),(322,true),(329,true),(331,false),(337,true)]
theorem inputList9223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 23) (closed_mem 6 23) inputClause9223 (by decide) v hb
mask_input "9223|4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648|281070345519754306582746209826974420904470159356012629248540137146423054831480967002693020367766683648"
def inputClause9230 : CNF.NClause := [(311,true),(315,true),(324,true),(328,false),(332,true),(339,true)]
theorem inputList9230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) inputClause9230 (by decide) v hb
mask_input "9230|546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456|1128655620702053439598997049062196425016979124781178917513253287721126787824629799192463929218449801216"
def inputClause9232 : CNF.NClause := [(311,true),(315,false),(324,true),(328,true),(332,true),(339,true)]
theorem inputList9232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) inputClause9232 (by decide) v hb
mask_input "9232|66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768|1129202366633654320051650099774547512559813835804385896976960669527679031630063212528252619295140347904"
def inputClause9233 : CNF.NClause := [(311,false),(315,true),(324,true),(328,true),(332,true),(339,true)]
theorem inputList9233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) inputClause9233 (by decide) v hb
mask_input "9233|4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048|1129202429211399513047062669941199060495910943305494950394522289069913635796656741257956233249107738624"
def inputClause9236 : CNF.NClause := [(310,true),(311,true),(312,true),(313,false),(314,true),(340,true)]
theorem inputList9236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) inputClause9236 (by decide) v hb
mask_input "9236|16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192|2239744790154075525187258584362877131539319946318833142520119675946171734374549317406983597302982115328"
def inputClause9238 : CNF.NClause := [(310,true),(311,false),(312,true),(313,true),(314,true),(340,true)]
theorem inputList9238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) inputClause9238 (by decide) v hb
mask_input "9238|4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048|2239744802669624563786341098396207441126539367819054953203631999854618655207868023152924320093775593472"
def inputClause9246 : CNF.NClause := [(310,true),(317,true),(324,true),(326,true),(333,true),(337,false)]
theorem inputList9246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) inputClause9246 (by decide) v hb
mask_input "9246|279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472|17669153845442098081845671270036191217211134063703161408516892211514199488009632167515482385199136768"
def inputClause9247 : CNF.NClause := [(310,true),(317,true),(324,true),(326,true),(333,false),(337,true)]
theorem inputList9247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) inputClause9247 (by decide) v hb
mask_input "9247|17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592|280139240819403529006545938524150755059591465770888653779609364980708559391934742954337063627965595648"
def inputClause9248 : CNF.NClause := [(310,true),(317,true),(324,true),(326,false),(333,true),(337,true)]
theorem inputList9248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) inputClause9248 (by decide) v hb
mask_input "9248|136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864|297500543447368686156252674951896874647082248128603527493738919169087561323079789344923699470586085376"
def inputClause9252 : CNF.NClause := [(310,true),(318,true),(321,true),(329,true),(332,true),(338,false)]
theorem inputList9252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) inputClause9252 (by decide) v hb
mask_input "9252|559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944|9847436318279215473875401159756562567550355440898393546567069223870208629666649053400148093098262528"
def inputClause9256 : CNF.NClause := [(310,true),(318,false),(321,true),(329,true),(332,true),(338,true)]
theorem inputList9256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) inputClause9256 (by decide) v hb
mask_input "9256|533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144|569783087865971287885715372546441089709933079073430188108371857704416220869775440238482015670478307328"
def inputClause9265 : CNF.NClause := [(310,true),(315,true),(320,true),(325,true),(330,false),(335,true)]
theorem inputList9265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 30) (closed_mem 6 30) inputClause9265 (by decide) v hb
mask_input "9265|2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824|70062579600761483907592934167384181640790129289040526266350693274634693808583672283977154762970759168"
def inputClause9267 : CNF.NClause := [(310,true),(315,true),(320,false),(325,true),(330,true),(335,true)]
theorem inputList9267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 30) (closed_mem 6 30) inputClause9267 (by decide) v hb
mask_input "9267|2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576|72247694338508574921883041372795633454028696015411382050006516839436824588057267566650644977906876416"
def inputClause9293 : CNF.NClause := [(344,false),(349,true),(354,true),(359,true),(364,true),(366,true)]
theorem inputList9293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) inputClause9293 (by decide) v hb
mask_input "9293|35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416|189095520640457411025044766586314115138265588509441026230478593424192710749181439698160924676100197667898916864"
def inputClause9295 : CNF.NClause := [(342,true),(347,true),(352,true),(357,true),(362,false),(366,true)]
theorem inputList9295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) inputClause9295 (by decide) v hb
mask_input "9295|9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904|150609762761141983494615180135078480262873541765908319807338590703421778647505616157586768621464845436808331264"
def inputClause9297 : CNF.NClause := [(342,true),(347,true),(352,false),(357,true),(362,true),(366,true)]
theorem inputList9297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) inputClause9297 (by decide) v hb
mask_input "9297|9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496|159994759097773356120126659238654620024613085701584926165672804234193067056459695992209284540791479746189852672"
def inputClause9298 : CNF.NClause := [(342,true),(347,false),(352,true),(357,true),(362,true),(366,true)]
theorem inputList9298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) inputClause9298 (by decide) v hb
mask_input "9298|286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328|160003646404910317647234151169623915611508672390917953255027287390945691382604538870840555862684781483225251840"
def inputClause9310 : CNF.NClause := [(345,true),(349,false),(353,true),(357,true),(361,true),(370,true)]
theorem inputList9310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) inputClause9310 (by decide) v hb
mask_input "9310|1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312|2409916677409559291229920901785773852101615527911118985087293965673854312120076174692802947054075451095564419072"
def inputClause9311 : CNF.NClause := [(345,false),(349,true),(353,true),(357,true),(361,true),(370,true)]
theorem inputList9311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) inputClause9311 (by decide) v hb
mask_input "9311|71671831749689734737838152978190216899892655911508785116799651230841339877765150252188079784691427704832|2409917752487035536575941969358068524954869026300957657719070717668622774740174341170056729875272221466979991552"
def inputClause9322 : CNF.NClause := [(344,true),(347,false),(355,true),(358,true),(361,true),(369,true)]
theorem inputList9322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) inputClause9322 (by decide) v hb
mask_input "9322|286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328|1207811450983071294575404312086642722205158690802084834261576543353124488117892162447640576607106721901856161792"
def inputClause9323 : CNF.NClause := [(344,false),(347,true),(355,true),(358,true),(361,true),(369,true)]
theorem inputList9323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) inputClause9323 (by decide) v hb
mask_input "9323|35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416|1207811701834482418489475894520178145870917840426380524542324452151903796062581734625666459265385968321853128704"
end Percolation.MaskChain
