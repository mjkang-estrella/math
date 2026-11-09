import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9152 : CNF.NClause := [(314,true),(317,true),(320,true),(328,false),(331,true),(338,true)]
theorem inputList9152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) inputClause9152 (by decide) v hb
mask_input "9152|546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456|564313123354229923776168306417979911906498431880294621654914537298101796012813706734793769613078298624"
def inputClause9154 : CNF.NClause := [(314,true),(317,false),(320,true),(328,true),(331,true),(338,true)]
theorem inputList9154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) inputClause9154 (by decide) v hb
mask_input "9154|266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072|564859669037046186643501132597046046053822398899952630182424736569503306485147828135530895037073195008"
def inputClause9162 : CNF.NClause := [(313,true),(319,true),(320,true),(326,true),(332,true),(336,false)]
theorem inputList9162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) inputClause9162 (by decide) v hb
mask_input "9162|139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736|8888926737383585439996901541331670574545050203416291413484378862214728499927743310174853779177865216"
def inputClause9166 : CNF.NClause := [(313,true),(319,false),(320,true),(326,true),(332,true),(336,true)]
theorem inputList9166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) inputClause9166 (by decide) v hb
mask_input "9166|1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288|148871905129978388144795846566006353181090592428320709018348724151647809338824912076204685627609841664"
def inputClause9169 : CNF.NClause := [(311,true),(318,true),(320,true),(327,true),(334,false),(337,true)]
theorem inputList9169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) inputClause9169 (by decide) v hb
mask_input "9169|34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184|280244173268467983480857346304354719238424560547253059460851734051100646074850167879013728772285267968"
def inputClause9170 : CNF.NClause := [(311,true),(318,true),(320,true),(327,false),(334,true),(337,true)]
theorem inputList9170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) inputClause9170 (by decide) v hb
mask_input "9170|273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728|314966778524398297780270819159846958413406125262682806889110842427858649937140260660187000457526247424"
def inputClause9187 : CNF.NClause := [(312,true),(318,true),(324,true),(325,true),(331,false),(336,true)]
theorem inputList9187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) inputClause9187 (by decide) v hb
mask_input "9187|4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648|140087116104295306137370711688403987996945371737183844883074146173445694606074778823470599777365786624"
def inputClause9189 : CNF.NClause := [(312,true),(318,true),(324,false),(325,true),(331,true),(336,true)]
theorem inputList9189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) inputClause9189 (by decide) v hb
mask_input "9189|34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216|144427441761286595424797395795340517893818067326612563311606534720540445088861040421117258738020909056"
def inputClause9199 : CNF.NClause := [(311,true),(319,true),(322,true),(325,true),(333,false),(338,true)]
theorem inputList9199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) inputClause9199 (by decide) v hb
mask_input "9199|17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592|560014153243111845390395493112163028045000846857135671778937783562449119092804131640608785697672790016"
def inputClause9211 : CNF.NClause := [(314,true),(315,true),(321,true),(327,true),(333,false),(336,true)]
theorem inputList9211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 21) (closed_mem 6 21) inputClause9211 (by decide) v hb
mask_input "9211|17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592|140261824825174790263211607623972285855256567166846446259441025486829247179661188325333610727125024768"
def inputClause9212 : CNF.NClause := [(314,true),(315,true),(321,true),(327,false),(333,true),(336,true)]
theorem inputList9212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 21) (closed_mem 6 21) inputClause9212 (by decide) v hb
mask_input "9212|273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728|157486424282841009167645062662523554107412776435130494196293969012307627048356273720718776996181573632"
def inputClause9228 : CNF.NClause := [(311,true),(315,true),(324,true),(328,true),(332,true),(339,false)]
theorem inputList9228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) inputClause9228 (by decide) v hb
mask_input "9228|1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888|9330062294347087301369034334753691297494668521577453172365179890833340484349170482831060876902006784"
def inputClause9253 : CNF.NClause := [(310,true),(318,true),(321,true),(329,true),(332,false),(338,true)]
theorem inputList9253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) inputClause9253 (by decide) v hb
mask_input "9253|8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296|561034618963598220415745962393397146636549052025987927525861262039178364427909381705725468702907826176"
def inputClause9277 : CNF.NClause := [(345,true),(350,true),(355,true),(360,true),(365,false),(366,true)]
theorem inputList9277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) inputClause9277 (by decide) v hb
mask_input "9277|75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232|152731025006458581862434133719004853838682552216339256381842370380944585928700346588956997695342384536159780864"
def inputClause9289 : CNF.NClause := [(344,true),(349,true),(354,true),(359,true),(364,false),(366,true)]
theorem inputList9289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) inputClause9289 (by decide) v hb
mask_input "9289|37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616|151518875151991954223680445956761211795363117673235864053554496279502981768017643485316866795983790765101809664"
def inputClause9290 : CNF.NClause := [(344,true),(349,true),(354,true),(359,false),(364,true),(366,true)]
theorem inputList9290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) inputClause9290 (by decide) v hb
mask_input "9290|1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488|187921285184986369255967395206995935719686197181314822049517506338252221657294074359004201270947705662096801792"
def inputClause9296 : CNF.NClause := [(342,true),(347,true),(352,true),(357,false),(362,true),(366,true)]
theorem inputList9296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) inputClause9296 (by decide) v hb
mask_input "9296|293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872|159710365269390587252686917447637161243954311642928059306329343218109088619824723876008602240205824161057079296"
def inputClause9309 : CNF.NClause := [(345,true),(349,true),(353,false),(357,true),(361,true),(370,true)]
theorem inputList9309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) inputClause9309 (by decide) v hb
mask_input "9309|18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992|2409899476169939365693583820629059086449559553673700222978865933757558910198505511056742421914927125152915259392"
def inputClause9314 : CNF.NClause := [(343,true),(350,true),(352,true),(359,false),(361,true),(368,true)]
theorem inputList9314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) inputClause9314 (by decide) v hb
mask_input "9314|1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488|605935471766686860575477732535663708045184305416456345925296037799419670804284390278962254723055822183528923136"
def inputClause9316 : CNF.NClause := [(343,true),(350,false),(352,true),(359,true),(361,true),(368,true)]
theorem inputList9316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) inputClause9316 (by decide) v hb
mask_input "9316|2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624|607107449559457787117910862013163074471931350125921337579525945696346388393965606015886034203695096409358336000"
def inputClause9319 : CNF.NClause := [(344,true),(347,true),(355,true),(358,true),(361,false),(369,true)]
theorem inputList9319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) inputClause9319 (by decide) v hb
mask_input "9319|4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952|1203114652504850626878564302245675960911274925274891840555302428608664993433022456621314187362656323261503111168"
def inputClause9331 : CNF.NClause := [(351,true),(352,true),(353,true),(354,true),(355,false),(371,true)]
theorem inputList9331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) inputClause9331 (by decide) v hb
mask_input "9331|73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968|4809884014479290152863004586851421294673621757113914143642244037363145691121000746757897649248599607579999469568"
def inputClause9332 : CNF.NClause := [(351,true),(352,true),(353,true),(354,false),(355,true),(371,true)]
theorem inputList9332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) inputClause9332 (by decide) v hb
mask_input "9332|36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984|4809920710457145994007190359985746128064674502153740836140223838784575881887018162514826769545449369590984343552"
def inputClause9333 : CNF.NClause := [(351,true),(352,true),(353,false),(354,true),(355,true),(371,true)]
theorem inputList9333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) inputClause9333 (by decide) v hb
mask_input "9333|18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992|4809939058446073914579283246552908544760200874673654182389213739495290977270026870393291329693874250596476780544"
def inputClause9340 : CNF.NClause := [(345,true),(348,false),(351,true),(359,true),(362,true),(369,true)]
theorem inputList9340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 11) (closed_mem 7 11) inputClause9340 (by decide) v hb
mask_input "9340|573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656|1213026902671748592037674687721636157003638529533781461291348378773715966158787315783766924890919040058795229184"
def inputClause9342 : CNF.NClause := [(343,true),(347,true),(351,true),(360,true),(364,true),(370,false)]
theorem inputList9342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) inputClause9342 (by decide) v hb
mask_input "9342|2404907604760405225358828131112281116032698930082119547604265954848982041717359046106827774346003151904701415424|39930115509672081198517027599359490947690021005207398276608168092244058348395001010387594808986373141483749376"
def inputClause9346 : CNF.NClause := [(343,true),(347,false),(351,true),(360,true),(364,true),(370,true)]
theorem inputList9346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) inputClause9346 (by decide) v hb
mask_input "9346|286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328|2444837433582750307798406207359028694219521351516703299845733655742621176700394536056614360402670386280474345472"
def inputClause9349 : CNF.NClause := [(344,true),(350,true),(351,true),(357,true),(363,false),(367,true)]
theorem inputList9349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) inputClause9349 (by decide) v hb
mask_input "9349|18788340662190665823115844774314696219005460391266558965658327772257672200916867547709591987078149624255479808|300913934749661227382741902845396201988440166220173944032135426893908057532107411155785770317747712798740185088"
def inputClause9352 : CNF.NClause := [(344,true),(350,false),(351,true),(357,true),(363,true),(367,true)]
theorem inputList9352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) inputClause9352 (by decide) v hb
mask_input "9352|2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624|319699981913235903134346136798815596120504830046451334716670017077326342810148190218687292286272752297309110272"
def inputClause9353 : CNF.NClause := [(344,false),(350,true),(351,true),(357,true),(363,true),(367,true)]
theorem inputList9353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) inputClause9353 (by decide) v hb
mask_input "9353|35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416|319702239575936018360990378700634409112337176665112547243401196266340114312354339820920236210785970077281812480"
def inputClause9355 : CNF.NClause := [(342,true),(349,true),(351,true),(358,true),(365,false),(368,true)]
theorem inputList9355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) inputClause9355 (by decide) v hb
mask_input "9355|75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232|601819779541313708536675272209274990756147757056811876510150795027183433847976119570236824905989728552578187264"
def inputClause9357 : CNF.NClause := [(342,true),(349,true),(351,false),(358,true),(365,true),(368,true)]
theorem inputList9357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) inputClause9357 (by decide) v hb
mask_input "9357|4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248|676968555192844391686115429664743171458288005491899775810536630938535348805891412791459052817196106798226997248"
def inputClause9358 : CNF.NClause := [(342,true),(349,false),(351,true),(358,true),(365,true),(368,true)]
theorem inputList9358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) inputClause9358 (by decide) v hb
mask_input "9358|1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312|676971995440768376793382845896086124588699200339383528232222237321794429190205545518671157845025771986756829184"
def inputClause9359 : CNF.NClause := [(342,false),(349,true),(351,true),(358,true),(365,true),(368,true)]
theorem inputList9359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) inputClause9359 (by decide) v hb
mask_input "9359|8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104|676973133231097403117921809076764653358392486135296123434185966516257718796476105040431411330792353963171643392"
def inputClause9364 : CNF.NClause := [(356,true),(357,false),(358,true),(359,true),(360,true),(371,true)]
theorem inputList9364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) inputClause9364 (by decide) v hb
mask_input "9364|293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872|4814071942952088023443205945806242905427516284784135424974188874583866212292738320017433503126578697083648212992"
def inputClause9369 : CNF.NClause := [(345,true),(347,true),(354,false),(356,true),(363,true),(368,true)]
theorem inputList9369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) inputClause9369 (by decide) v hb
mask_input "9369|36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984|620162384122874085188239659280449199742475672534382773402569606168480099901025680927884277701376909101508853760"
def inputClause9370 : CNF.NClause := [(345,true),(347,false),(354,true),(356,true),(363,true),(368,true)]
theorem inputList9370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) inputClause9370 (by decide) v hb
mask_input "9370|286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328|620198793413402927573486481062162120372660818003585819865408940391305367301683585624212389245907532346782908416"
def inputClause9373 : CNF.NClause := [(343,true),(349,true),(355,true),(356,true),(362,false),(367,true)]
theorem inputList9373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) inputClause9373 (by decide) v hb
mask_input "9373|9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904|300834791129451632493157645064970035441428459754883660456170200879036400982547388988619791630645467289697124352"
def inputClause9384 : CNF.NClause := [(342,true),(350,true),(353,true),(356,true),(364,true),(369,false)]
theorem inputList9384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) inputClause9384 (by decide) v hb
mask_input "9384|1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712|37744115682327575577796121703755567058466182513324391391947639129746993626955679207052076852043311510057910272"
def inputClause9386 : CNF.NClause := [(342,true),(350,true),(353,true),(356,false),(364,true),(369,true)]
theorem inputList9386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) inputClause9386 (by decide) v hb
mask_input "9386|146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936|1240051134151106823680467094722596791510604667395077395202161410868517251421565539232749482837645839418469122048"
end Percolation.MaskChain
