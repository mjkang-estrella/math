import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9085 : CNF.NClause := [(335,true),(336,true),(337,true),(338,true),(339,false),(340,true)]
theorem inputList9085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) inputClause9085 (by decide) v hb
mask_input "9085|1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888|3289625090073649934256243349584902533491166824063391504384358992040569310795861388528163818242672951296"
def inputClause9086 : CNF.NClause := [(335,true),(336,true),(337,true),(338,false),(339,true),(340,true)]
theorem inputList9086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) inputClause9086 (by decide) v hb
mask_input "9086|559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944|3849561275618100986895603919727013603021578198372053888109356267281517278590901624873383191560574730240"
def inputClause9087 : CNF.NClause := [(335,true),(336,true),(337,false),(338,true),(339,true),(340,true)]
theorem inputList9087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) inputClause9087 (by decide) v hb
mask_input "9087|279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472|4129529368390326513215284204798069137786783885526385079971854904901991262488421743045992878219525619712"
def inputClause9088 : CNF.NClause := [(335,true),(336,false),(337,true),(338,true),(339,true),(340,true)]
theorem inputList9088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) inputClause9088 (by decide) v hb
mask_input "9088|139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736|4269513414776439276375124347333596905169386729103550675903104223712228254437181802132297721549001064448"
def inputClause9094 : CNF.NClause := [(314,true),(319,false),(324,true),(329,true),(334,true),(335,true)]
theorem inputList9094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) inputClause9094 (by decide) v hb
mask_input "9094|1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288|106115869319348249157604715784717507952714151337936671433668557499132998198965437847649350587791704064"
def inputClause9099 : CNF.NClause := [(312,true),(317,true),(322,false),(327,true),(332,true),(335,true)]
theorem inputList9099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) inputClause9099 (by decide) v hb
mask_input "9099|8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304|79014707774865154947771951687890882742210518695897134303152089142391810429088981637145314917414338560"
def inputClause9101 : CNF.NClause := [(312,false),(317,true),(322,true),(327,true),(332,true),(335,true)]
theorem inputList9101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) inputClause9101 (by decide) v hb
mask_input "9101|8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096|79023243379309479522046522419162021225855981847172020458556994703191818752446300368718258238566432768"
def inputClause9104 : CNF.NClause := [(313,true),(318,true),(323,true),(328,false),(333,true),(335,true)]
theorem inputList9104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) inputClause9104 (by decide) v hb
mask_input "9104|546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456|87507667571765542615189866724887832868698144881667020753732652560925214391804334874732513572530683904"
def inputClause9106 : CNF.NClause := [(313,true),(318,false),(323,true),(328,true),(333,true),(335,true)]
theorem inputList9106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) inputClause9106 (by decide) v hb
mask_input "9106|533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144|88053946256202315368762393526240695822007786563259734699646608452125747086672733695400886126264713216"
def inputClause9115 : CNF.NClause := [(330,true),(331,true),(332,true),(333,true),(334,false),(340,true)]
theorem inputList9115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) inputClause9115 (by decide) v hb
mask_input "9115|34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184|2272553503049549389423029813975208598601943038698047721446375660059941166168151584229230190926952923136"
def inputClause9119 : CNF.NClause := [(330,false),(331,true),(332,true),(333,true),(334,true),(340,true)]
theorem inputList9119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) inputClause9119 (by decide) v hb
mask_input "9119|2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824|2305362263921294568288617347381972919082240580161445907992762219156090461156142223077582888582298730496"
def inputClause9126 : CNF.NClause := [(312,true),(319,true),(321,true),(328,true),(330,true),(337,false)]
theorem inputList9126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) inputClause9126 (by decide) v hb
mask_input "9126|279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472|2739411717267926246726624693715990311790916216736947633131963467663277353859475336031597403691810816"
def inputClause9131 : CNF.NClause := [(312,false),(319,true),(321,true),(328,true),(330,true),(337,true)]
theorem inputList9131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) inputClause9131 (by decide) v hb
mask_input "9131|8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096|282707496145794093500351900409217985352183655704253599039955718482505980695833789678014135535447048192"
def inputClause9136 : CNF.NClause := [(313,true),(316,false),(324,true),(327,true),(330,true),(338,true)]
theorem inputList9136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 8) (closed_mem 6 8) inputClause9136 (by decide) v hb
mask_input "9136|133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536|562431035089805393747707974206024185849893228524404035071645185050146881545843632168900490089835003904"
def inputClause9143 : CNF.NClause := [(311,false),(317,true),(323,true),(329,true),(330,true),(336,true)]
theorem inputList9143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) inputClause9143 (by decide) v hb
mask_input "9143|4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048|143282277367954138440818355427566827041563744697749562389643794432915476982831090675609049661966385152"
def inputClause9165 : CNF.NClause := [(313,true),(319,true),(320,false),(326,true),(332,true),(336,true)]
theorem inputList9165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) inputClause9165 (by decide) v hb
mask_input "9165|2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576|148870837136460427689754649055153268405033291076059530691963750630843898228962021755929674146566373376"
def inputClause9171 : CNF.NClause := [(311,true),(318,true),(320,false),(327,true),(334,true),(337,true)]
theorem inputList9171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) inputClause9171 (by decide) v hb
mask_input "9171|2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576|315238048877960253360734986916530491531960668737022101790894116712052071842314402010039916642567192576"
def inputClause9172 : CNF.NClause := [(311,true),(318,false),(320,true),(327,true),(334,true),(337,true)]
theorem inputList9172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) inputClause9172 (by decide) v hb
mask_input "9172|533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144|315239650868237194043296783182810118696046620765413869280471576993257938507108737490452433864132395008"
def inputClause9178 : CNF.NClause := [(325,true),(326,false),(327,true),(328,true),(329,true),(340,true)]
theorem inputList9178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) inputClause9178 (by decide) v hb
mask_input "9178|136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864|2241726938147138815113904860711769622483996807031396508670499955575850891085685379811298802088284258304"
def inputClause9179 : CNF.NClause := [(325,false),(326,true),(327,true),(328,true),(329,true),(340,true)]
theorem inputList9179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) inputClause9179 (by decide) v hb
mask_input "9179|68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432|2241795289732288284236541501406367048151664093576111921559138260907301202116910360308899536875066228736"
def inputClause9184 : CNF.NClause := [(314,true),(316,false),(323,true),(325,true),(332,true),(337,true)]
theorem inputList9184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 16) (closed_mem 6 16) inputClause9184 (by decide) v hb
mask_input "9184|133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536|288802568527591846684686132269986961210454263726056469541699132132951806905532062810013251959303176192"
def inputClause9186 : CNF.NClause := [(312,true),(318,true),(324,true),(325,true),(331,true),(336,false)]
theorem inputList9186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) inputClause9186 (by decide) v hb
mask_input "9186|139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736|4477571167748566826275573607111463345048867021804673824676368576028608655713471583612782801936449536"
def inputClause9191 : CNF.NClause := [(312,false),(318,true),(324,true),(325,true),(331,true),(336,true)]
theorem inputList9191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) inputClause9191 (by decide) v hb
mask_input "9191|8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096|144461609210161970920060706787085691002838762932155729300250804780634320048927726839290477604216242176"
def inputClause9195 : CNF.NClause := [(313,true),(317,true),(321,false),(325,true),(334,true),(339,true)]
theorem inputList9195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) inputClause9195 (by decide) v hb
mask_input "9195|4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152|1154937017956357973437188134701521857217780966728025954814391194107369033497052798200938742179606560768"
def inputClause9201 : CNF.NClause := [(311,true),(319,true),(322,false),(325,true),(333,true),(338,true)]
theorem inputList9201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) inputClause9201 (by decide) v hb
mask_input "9201|8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304|577503615093232257145045930842279320759367791486191944659264160247297454207496016464196799265509474304"
def inputClause9202 : CNF.NClause := [(311,true),(319,false),(322,true),(325,true),(333,true),(338,true)]
theorem inputList9202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) inputClause9202 (by decide) v hb
mask_input "9202|1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288|577511091047857980330334313418250914191768900952020192943958974892924831976536248706121879632813752320"
def inputClause9203 : CNF.NClause := [(311,false),(319,true),(322,true),(325,true),(333,true),(338,true)]
theorem inputList9203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) inputClause9203 (by decide) v hb
mask_input "9203|4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048|577512154869526261252348006251327229105419728470874101042506507110913102808626237111083316850259394560"
def inputClause9208 : CNF.NClause := [(315,true),(316,false),(317,true),(318,true),(319,true),(340,true)]
theorem inputList9208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 20) (closed_mem 6 20) inputClause9208 (by decide) v hb
mask_input "9208|133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536|2239746677916055513882204451056865494278249355935622920616561865470248960066787434086375951580998402048"
def inputClause9220 : CNF.NClause := [(312,true),(315,false),(323,true),(326,true),(334,true),(338,true)]
theorem inputList9220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) inputClause9220 (by decide) v hb
mask_input "9220|66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768|595085996551264908021308056694390758853126427595378002162920674544901696158032261067024385947725725696"
def inputClause9225 : CNF.NClause := [(313,true),(315,true),(322,false),(329,true),(331,true),(337,true)]
theorem inputList9225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 23) (closed_mem 6 23) inputClause9225 (by decide) v hb
mask_input "9225|8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304|285436303021176646791161634194384985426718087399709627510311890192811671950976596286939954873465044992"
def inputClause9226 : CNF.NClause := [(313,true),(315,false),(322,true),(329,true),(331,true),(337,true)]
theorem inputList9226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 23) (closed_mem 6 23) inputClause9226 (by decide) v hb
mask_input "9226|66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768|285444780219725457903051139436781345836672916883282730475992617514192716385513288204122858504247574528"
def inputClause9235 : CNF.NClause := [(310,true),(311,true),(312,true),(313,true),(314,false),(340,true)]
theorem inputList9235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) inputClause9235 (by decide) v hb
mask_input "9235|33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384|2239744773466676807055148565651770052089694050985204061608769910734909173263457709745729300248590811136"
def inputClause9242 : CNF.NClause := [(310,true),(319,true),(323,true),(327,false),(331,true),(339,true)]
theorem inputList9242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) inputClause9242 (by decide) v hb
mask_input "9242|273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728|1124265030514198296629680254761848207915706447384254858985309362199790150595034810939217755299387539456"
def inputClause9244 : CNF.NClause := [(310,true),(319,false),(323,true),(327,true),(331,true),(339,true)]
theorem inputList9244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) inputClause9244 (by decide) v hb
mask_input "9244|1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288|1124537368861278212665185620029384825810318292210855332213477610004787483610071842609345682965471952896"
def inputClause9249 : CNF.NClause := [(310,true),(317,true),(324,false),(326,true),(333,true),(337,true)]
theorem inputList9249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) inputClause9249 (by decide) v hb
mask_input "9249|34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216|297603070825092889840207635993793013148583177945676646826696377166263027869917260091324801650759041024"
def inputClause9250 : CNF.NClause := [(310,true),(317,false),(324,true),(326,true),(333,true),(337,true)]
theorem inputList9250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) inputClause9250 (by decide) v hb
mask_input "9250|266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072|297636979619288134287765656963378454788402495879969058689419286451787205608064027760056416173889159168"
def inputClause9254 : CNF.NClause := [(310,true),(318,true),(321,true),(329,false),(332,true),(338,true)]
theorem inputList9254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) inputClause9254 (by decide) v hb
mask_input "9254|1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912|568689996500338762151049720188308821415285145034114171053351459161613199925107197437007764822488514560"
def inputClause9262 : CNF.NClause := [(310,true),(316,false),(322,true),(328,true),(334,true),(336,true)]
theorem inputList9262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 29) (closed_mem 6 29) inputClause9262 (by decide) v hb
mask_input "9262|133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536|175535416697905230337736636151902177709253494563973359748166599982237837203539491358543811436246728704"
def inputClause9268 : CNF.NClause := [(310,true),(315,false),(320,true),(325,true),(330,true),(335,true)]
theorem inputList9268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 30) (closed_mem 6 30) inputClause9268 (by decide) v hb
mask_input "9268|66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768|72249763575949623303525361550073485207639717385417415057377403035994402363416617562183479722428596224"
def inputClause9271 : CNF.NClause := [(366,true),(367,true),(368,true),(369,true),(370,false),(371,true)]
theorem inputList9271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) inputClause9271 (by decide) v hb
mask_input "9271|2404907604760405225358828131112281116032698930082119547604265954848982041717359046106827774346003151904701415424|7064416088983690349491557635142325778346053107116226171087531242368884747544742197938806587141384258720060407808"
end Percolation.MaskChain
