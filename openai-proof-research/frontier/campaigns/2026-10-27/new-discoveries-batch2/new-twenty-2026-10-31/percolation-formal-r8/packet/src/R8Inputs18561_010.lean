import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9387 : CNF.NClause := [(342,true),(350,true),(353,false),(356,true),(364,true),(369,true)]
theorem inputList9387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) inputClause9387 (by decide) v hb
mask_input "9387|18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992|1240179570073602267685117300692733708379289275034470818945090715843522919102626494382001403876620006456916180992"
def inputClause9388 : CNF.NClause := [(342,true),(350,false),(353,true),(356,true),(364,true),(369,true)]
theorem inputList9388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) inputClause9388 (by decide) v hb
mask_input "9388|2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624|1240195624563914198185698576439000822987874850989394996912956878965398627562759113775657894006491777336722063360"
def inputClause9397 : CNF.NClause := [(345,true),(346,true),(352,true),(358,true),(364,false),(367,true)]
theorem inputList9397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 21) (closed_mem 7 21) inputClause9397 (by decide) v hb
mask_input "9397|37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616|301209975250703320832076543336272616679345172835416431069060367853317047686472520108902433181298380740874993664"
def inputClause9399 : CNF.NClause := [(345,true),(346,true),(352,false),(358,true),(364,true),(367,true)]
theorem inputList9399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 21) (closed_mem 7 21) inputClause9399 (by decide) v hb
mask_input "9399|9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496|338777482580620692192261789601320800769592907357992875875882073042474844396801901265089337081242239486639734784"
def inputClause9402 : CNF.NClause := [(343,true),(346,true),(354,true),(357,true),(365,true),(369,false)]
theorem inputList9402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) inputClause9402 (by decide) v hb
mask_input "9402|1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712|75483787711086670392038497442026486323484571681982269239218036681117675090838936974788518043139972151598120960"
def inputClause9404 : CNF.NClause := [(343,true),(346,true),(354,true),(357,false),(365,true),(369,true)]
theorem inputList9404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) inputClause9404 (by decide) v hb
mask_input "9404|293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872|1277644022268442553917966377923568377211412076404428503057512602734167169821379133972769442841343452016069836800"
def inputClause9405 : CNF.NClause := [(343,true),(346,true),(354,false),(357,true),(365,true),(369,true)]
theorem inputList9405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) inputClause9405 (by decide) v hb
mask_input "9405|36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984|1277900894113433441927266789863842210948781291683215350543371212684178505183501044271273284919291786092963954688"
def inputClause9406 : CNF.NClause := [(343,true),(346,false),(354,true),(357,true),(365,true),(369,true)]
theorem inputList9406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) inputClause9406 (by decide) v hb
mask_input "9406|143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664|1277937446747625783691983087321861087959400236937730220023780780506306234266838704497901900839981978721093419008"
def inputClause9407 : CNF.NClause := [(343,false),(346,true),(354,true),(357,true),(365,true),(369,true)]
theorem inputList9407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) inputClause9407 (by decide) v hb
mask_input "9407|17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208|1277937572173331345649018878538628799792279811749878065164154734905695888239183490586914842169121601931091902464"
def inputClause9408 : CNF.NClause := [(344,true),(346,true),(353,true),(360,true),(362,true),(368,false)]
theorem inputList9408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) inputClause9408 (by decide) v hb
mask_input "9408|601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856|11761240082376460935877134146491547307947034996094724374489147567504217611931444508658685610548186249221373952"
def inputClause9410 : CNF.NClause := [(344,true),(346,true),(353,true),(360,false),(362,true),(368,true)]
theorem inputList9410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) inputClause9410 (by decide) v hb
mask_input "9410|2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976|610639598689703934047694686327772489288746084967716291404848345308217519016156597591901930198664205522364792832"
def inputClause9411 : CNF.NClause := [(344,true),(346,true),(353,false),(360,true),(362,true),(368,true)]
theorem inputList9411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) inputClause9411 (by decide) v hb
mask_input "9411|18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992|612969793283549846703491280357399409620595394996711265026565735569034632658262498156901069048624093219904290816"
def inputClause9413 : CNF.NClause := [(344,false),(346,true),(353,true),(360,true),(362,true),(368,true)]
theorem inputList9413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) inputClause9413 (by decide) v hb
mask_input "9413|35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416|612988105436561892430716798005485337221013317570296655521163077879924112620601267152790503103009081879682875392"
def inputClause9417 : CNF.NClause := [(342,true),(346,true),(355,false),(359,true),(363,true),(370,true)]
theorem inputList9417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) inputClause9417 (by decide) v hb
mask_input "9417|73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968|2424870369016625275886575034091065559419603144019734078461446301306264683968680458127213501731943228349756735488"
def inputClause9418 : CNF.NClause := [(342,true),(346,false),(355,true),(359,true),(363,true),(370,true)]
theorem inputList9418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) inputClause9418 (by decide) v hb
mask_input "9418|143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664|2424943617628673458795477104683409269821274834314075640439835670549822603818035534110771237949483182988871073792"
def inputClause9422 : CNF.NClause := [(341,true),(342,true),(343,true),(344,false),(345,true),(371,true)]
theorem inputList9422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) inputClause9422 (by decide) v hb
mask_input "9422|35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416|4809815312549068590896649947866907138213834653759931968002410515097462727769144166501059036212370994303330156544"
def inputClause9438 : CNF.NClause := [(341,true),(349,true),(352,true),(360,true),(363,true),(369,false)]
theorem inputList9438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) inputClause9438 (by decide) v hb
mask_input "9438|1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712|21147208468225938728415995180017453774503283725917130570721507693545324306557616533131496830706900436091142144"
def inputClause9439 : CNF.NClause := [(341,true),(349,true),(352,true),(360,true),(363,false),(369,true)]
theorem inputList9439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) inputClause9439 (by decide) v hb
mask_input "9439|18788340662190665823115844774314696219005460391266558965658327772257672200916867547709591987078149624255479808|1204812670186237885584714215961843315571847288375710345407196157345778672964320272038835792016630326764186370048"
def inputClause9442 : CNF.NClause := [(341,true),(349,false),(352,true),(360,true),(363,true),(369,true)]
theorem inputList9442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) inputClause9442 (by decide) v hb
mask_input "9442|1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312|1223599864099120556372074255325710360747382350484482320232292616323616651703799095344141348994431921325598572544"
def inputClause9452 : CNF.NClause := [(341,true),(346,true),(351,true),(356,false),(361,true),(366,true)]
theorem inputList9452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) inputClause9452 (by decide) v hb
mask_input "9452|146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936|155008545283457956918806837821077365497998997386530265515797982698085233113579832128842669068415510577550458880"
def inputClause9457 : CNF.NClause := [(397,true),(398,true),(399,true),(400,true),(401,false),(402,true)]
theorem inputList9457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) inputClause9457 (by decide) v hb
mask_input "9457|5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343945494986752|15170718033760587964228525135517694761687021532871688137880123719676304779348942018449166450520809759685931135339891523584"
def inputClause9459 : CNF.NClause := [(397,true),(398,true),(399,false),(400,true),(401,true),(402,true)]
theorem inputList9459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) inputClause9459 (by decide) v hb
mask_input "9459|1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688|19044092850890950848712403893522212573181580222115523407126112754487276212374203810393634480441016506839785893299012763648"
def inputClause9460 : CNF.NClause := [(397,true),(398,false),(399,true),(400,true),(401,true),(402,true)]
theorem inputList9460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) inputClause9460 (by decide) v hb
mask_input "9460|645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344|19689655320412677996126383686522965541764006670322829285333777593622438117878414109051045818761050964698761686292199636992"
def inputClause9464 : CNF.NClause := [(376,true),(381,true),(386,true),(391,false),(396,true),(397,true)]
theorem inputList9464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) inputClause9464 (by decide) v hb
mask_input "9464|5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448|484334539330942192453169918755978210029757216172701603878904962734685053065315819897809538425304801815451893986240757760"
def inputClause9465 : CNF.NClause := [(376,true),(381,true),(386,false),(391,true),(396,true),(397,true)]
theorem inputList9465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) inputClause9465 (by decide) v hb
mask_input "9465|157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264|489220388099295107875492519728396018141587103842239319265730551116811522564981474013624907440910531354911915857038802944"
def inputClause9469 : CNF.NClause := [(374,true),(379,true),(384,true),(389,true),(394,false),(397,true)]
theorem inputList9469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) inputClause9469 (by decide) v hb
mask_input "9469|40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584|324082770756559905014954094284934450831210120764613382202995848302345221833082584044458684351493285835298720902620905472"
def inputClause9471 : CNF.NClause := [(374,true),(379,true),(384,false),(389,true),(394,true),(397,true)]
theorem inputList9471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) inputClause9471 (by decide) v hb
mask_input "9471|39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816|364391023095471457249115552307381367753806694038299534144306952454888595205324230499935478730240554535843901336704778240"
def inputClause9472 : CNF.NClause := [(374,true),(379,false),(384,true),(389,true),(394,true),(397,true)]
theorem inputList9472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) inputClause9472 (by decide) v hb
mask_input "9472|1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088|364429193788974214400852447627478381879680365035717797545766527364123958248290368422715286300674974297870932757570387968"
def inputClause9473 : CNF.NClause := [(374,false),(379,true),(384,true),(389,true),(394,true),(397,true)]
theorem inputList9473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) inputClause9473 (by decide) v hb
mask_input "9473|38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784|364430386623146175561844225606231413571113917254387118277062139080037563343383060232802155287251049915434277489472438272"
def inputClause9478 : CNF.NClause := [(375,true),(380,false),(385,true),(390,true),(395,true),(397,true)]
theorem inputList9478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 3) (closed_mem 8 3) inputClause9478 (by decide) v hb
mask_input "9478|2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176|406077152817084855094714998754580279468147505967782655987700635160666963744475587516724903441332719666253969018547339264"
def inputClause9481 : CNF.NClause := [(373,true),(378,true),(383,true),(388,true),(393,false),(397,true)]
theorem inputList9481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) inputClause9481 (by decide) v hb
mask_input "9481|20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792|323432002758711739360971995392655467561211672434133160653414133934963087292593866686582176755755257382393308699607171072"
def inputClause9482 : CNF.NClause := [(373,true),(378,true),(383,true),(388,false),(393,true),(397,true)]
theorem inputList9482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) inputClause9482 (by decide) v hb
mask_input "9482|630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056|342975397832123401050262399282326700008531223112284022200716487463468965291256483149843652818178175540233396182799351808"
def inputClause9485 : CNF.NClause := [(373,false),(378,true),(383,true),(388,true),(393,true),(397,true)]
theorem inputList9485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) inputClause9485 (by decide) v hb
mask_input "9485|19239260838083241802870625048898248928261591440656956380834127638791856333738872368854622194768025215237611323392|343605810692004874634417061053303948931163570679020028690447279323809258047744104780753912223634139422461086993032937472"
def inputClause9487 : CNF.NClause := [(392,true),(393,true),(394,true),(395,true),(396,false),(402,true)]
theorem inputList9487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) inputClause9487 (by decide) v hb
mask_input "9487|161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336|10480303216141789158798828201996598974330329370115481366527558872834894059669914067266412195539309401804310139373768146944"
def inputClause9489 : CNF.NClause := [(392,true),(393,true),(394,false),(395,true),(396,true),(402,true)]
theorem inputList9489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) inputClause9489 (by decide) v hb
mask_input "9489|40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584|10601346179177112998938949413184240155939534329154351218691496030172736916951953498264676821474315862652868100559990685696"
def inputClause9490 : CNF.NClause := [(392,true),(393,false),(394,true),(395,true),(396,true),(402,true)]
theorem inputList9490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) inputClause9490 (by decide) v hb
mask_input "9490|20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792|10621520006349666972295636281715513686207735155660829527385485556395710726498960070097720925796816939460961094091027775488"
def inputClause9491 : CNF.NClause := [(392,false),(393,true),(394,true),(395,true),(396,true),(402,true)]
theorem inputList9491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) inputClause9491 (by decide) v hb
mask_input "9491|10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896|10631606919935943958973979715981150451341835568914068681732480319507197631272463356014242977958067477865007590856546320384"
def inputClause9496 : CNF.NClause := [(376,true),(380,false),(384,true),(388,true),(392,true),(401,true)]
theorem inputList9496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 6) (closed_mem 8 6) inputClause9496 (by decide) v hb
mask_input "9496|2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176|5175256657779519576802724944918363346414189780572015617857319643853675436412151797667185752084836802985948275287739334656"
def inputClause9499 : CNF.NClause := [(374,true),(381,true),(383,true),(390,true),(392,false),(399,true)]
theorem inputList9499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) inputClause9499 (by decide) v hb
mask_input "9499|10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896|1293671332172417964213536724709227816003504031088148467220158598399828468361616272028330061306035242927289144795469971456"
def inputClause9500 : CNF.NClause := [(374,true),(381,true),(383,true),(390,false),(392,true),(399,true)]
theorem inputList9500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) inputClause9500 (by decide) v hb
mask_input "9500|2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224|1301236517362125704222294300408455389854079341028077832980404670733443646941743736465721600426973146730324017369608880128"
end Percolation.MaskChain
