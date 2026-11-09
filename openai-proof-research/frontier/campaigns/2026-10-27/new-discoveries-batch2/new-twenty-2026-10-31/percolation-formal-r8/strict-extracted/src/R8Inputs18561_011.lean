import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9501 : CNF.NClause := [(374,true),(381,true),(383,false),(390,true),(392,true),(399,true)]
theorem inputList9501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) inputClause9501 (by decide) v hb
mask_input "9501|19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408|1303738544755596753652274019454814509330701904471752388843819387364613250274233809339546406334158338873515238246993362944"
def inputClause9502 : CNF.NClause := [(374,true),(381,false),(383,true),(390,true),(392,true),(399,true)]
theorem inputList9502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) inputClause9502 (by decide) v hb
mask_input "9502|4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352|1303753320507920401581978624094852063185878809373978813386319867974639842419898120793525686684003920716880540732489728000"
def inputClause9503 : CNF.NClause := [(374,false),(381,true),(383,true),(390,true),(392,true),(399,true)]
theorem inputList9503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) inputClause9503 (by decide) v hb
mask_input "9503|38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784|1303758207280173274725396553233614483341106587818204740253240599843060095551406890467107375758041391795285211085765869568"
def inputClause9506 : CNF.NClause := [(375,true),(378,true),(386,true),(389,false),(392,true),(400,true)]
theorem inputList9506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 8) (closed_mem 8 8) inputClause9506 (by decide) v hb
mask_input "9506|1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112|2592495092311361325247816625771550974255987942456836392614755622854346506184258483988018341272806921151420643804234907648"
def inputClause9510 : CNF.NClause := [(373,true),(379,true),(385,true),(391,true),(392,true),(398,false)]
theorem inputList9510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 9) (closed_mem 8 9) inputClause9510 (by decide) v hb
mask_input "9510|645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344|15210424943762744386656896069283613314941116361843305115992795472335370074459616322709882324828237358990348848994451456"
def inputClause9513 : CNF.NClause := [(373,true),(379,true),(385,false),(391,true),(392,true),(398,true)]
theorem inputList9513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 9) (closed_mem 8 9) inputClause9513 (by decide) v hb
mask_input "9513|78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632|660694090453097102842212130989836294669757405090608252430321738020688784135126920558898392112352925386684528586200711168"
def inputClause9517 : CNF.NClause := [(382,true),(383,true),(384,true),(385,true),(386,false),(402,true)]
theorem inputList9517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) inputClause9517 (by decide) v hb
mask_input "9517|157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264|10329147269870870837920722734412423035870592220339158296747642232262856409524007893058374216619007144177265712745953624064"
def inputClause9518 : CNF.NClause := [(382,true),(383,true),(384,true),(385,false),(386,true),(402,true)]
theorem inputList9518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) inputClause9518 (by decide) v hb
mask_input "9518|78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632|10329226073883263626879147292492623323098202379817699227640978128849664900967550887479597045151516914008547326001934237696"
def inputClause9519 : CNF.NClause := [(382,true),(383,true),(384,false),(385,true),(386,true),(402,true)]
theorem inputList9519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) inputClause9519 (by decide) v hb
mask_input "9519|39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816|10329265475889460021358359571532723466712007459556969693087646077143069146689322384690208459417771798924188132629924544512"
def inputClause9520 : CNF.NClause := [(382,true),(383,false),(384,true),(385,true),(386,true),(402,true)]
theorem inputList9520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) inputClause9520 (by decide) v hb
mask_input "9520|19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408|10329285176892558218597965711052773538518909999426604925810980051289771269550208133295514166550899241382008535943919697920"
def inputClause9523 : CNF.NClause := [(376,true),(379,true),(382,true),(390,true),(393,false),(400,true)]
theorem inputList9523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) inputClause9523 (by decide) v hb
mask_input "9523|20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792|2584782842211807276938717907014449622190605000911934645079934454449060402654315919610239277419812210563640494929139990528"
def inputClause9525 : CNF.NClause := [(376,true),(379,true),(382,false),(390,true),(393,true),(400,true)]
theorem inputList9525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) inputClause9525 (by decide) v hb
mask_input "9525|9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704|2604946818882812151675601705785698116555354557483595337412256993598683150770879617140630528175749566142823286803179503616"
def inputClause9527 : CNF.NClause := [(376,false),(379,true),(382,true),(390,true),(393,true),(400,true)]
theorem inputList9527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) inputClause9527 (by decide) v hb
mask_input "9527|153914086704665934422965000391185991426092731525255651046673021110334850669910978950836977558144201721900890587136|2604956515470274545629470352580722761272814401325681428518272933999013101866471821532304430905335729227531766559286493184"
def inputClause9530 : CNF.NClause := [(374,true),(378,true),(382,true),(391,false),(395,true),(401,true)]
theorem inputList9530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 12) (closed_mem 8 12) inputClause9530 (by decide) v hb
mask_input "9530|5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448|5245205569500450666188610185492394568176129722513286859135460753406881262575266898015780518473998313445945837805425917952"
def inputClause9535 : CNF.NClause := [(375,true),(381,true),(382,true),(388,true),(394,false),(398,true)]
theorem inputList9535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 13) (closed_mem 8 13) inputClause9535 (by decide) v hb
mask_input "9535|40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584|646207754330236459344048073764893015851480341984225512524678015776166984365643900436662722348446977424694862476973441024"
def inputClause9544 : CNF.NClause := [(373,true),(380,false),(382,true),(389,true),(396,true),(399,true)]
theorem inputList9544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 14) (closed_mem 8 14) inputClause9544 (by decide) v hb
mask_input "9544|2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176|1453786290362980641719292336165548859753922258319502177279243601350528850703460290760265990161419763480136763224969183232"
def inputClause9549 : CNF.NClause := [(387,true),(388,true),(389,false),(390,true),(391,true),(402,true)]
theorem inputList9549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) inputClause9549 (by decide) v hb
mask_input "9549|1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112|10337510345686055566133528960673678517900720394999314587802914257537907563970008176010646894631606467522026919536896245760"
def inputClause9550 : CNF.NClause := [(387,true),(388,false),(389,true),(390,true),(391,true),(402,true)]
theorem inputList9550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) inputClause9550 (by decide) v hb
mask_input "9550|630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056|10338140777785197877800925425315280815721601670827642034949601430232375495518352131380429522891684626172279825584741154816"
def inputClause9551 : CNF.NClause := [(387,false),(388,true),(389,true),(390,true),(391,true),(402,true)]
theorem inputList9551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) inputClause9551 (by decide) v hb
mask_input "9551|315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528|10338455993834769033634623657636081964632042308741805758522945016579609461292524109065320837021723705497406278608663609344"
def inputClause9553 : CNF.NClause := [(376,true),(378,true),(385,true),(387,true),(394,false),(399,true)]
theorem inputList9553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 16) (closed_mem 8 16) inputClause9553 (by decide) v hb
mask_input "9553|40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584|1291519728675851762949754491227509329232860824270974037160264394569471819900388918975831573487505555595368261770729750528"
def inputClause9554 : CNF.NClause := [(376,true),(378,true),(385,true),(387,false),(394,true),(399,true)]
theorem inputList9554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 16) (closed_mem 8 16) inputClause9554 (by decide) v hb
mask_input "9554|315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528|1331552166971388553829429995969255240858821839369766930974899860668185473220230084957028468002468629886427795808881475584"
def inputClause9556 : CNF.NClause := [(376,true),(378,false),(385,true),(387,true),(394,true),(399,true)]
theorem inputList9556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 16) (closed_mem 8 16) inputClause9556 (by decide) v hb
mask_input "9556|615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544|1331866767364612890999390536430054825025296772913004553525639260323334997654999382998003978784597476634747361229241581568"
def inputClause9564 : CNF.NClause := [(375,true),(379,true),(383,true),(387,true),(396,true),(401,false)]
theorem inputList9564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 18) (closed_mem 8 18) inputClause9564 (by decide) v hb
mask_input "9564|5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343945494986752|161726842702838129587241915293542787943876911623843390521627666998406002857340995197870937957484380473405440743784316928"
def inputClause9568 : CNF.NClause := [(375,true),(379,false),(383,true),(387,true),(396,true),(401,true)]
theorem inputList9568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 18) (closed_mem 8 18) inputClause9568 (by decide) v hb
mask_input "9568|1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088|5326225367563961671571604875579563407115357088540438214137738006695532364212218025169330037821939578191598009482154606592"
def inputClause9573 : CNF.NClause := [(373,true),(381,true),(384,false),(387,true),(395,true),(400,true)]
theorem inputList9573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 19) (closed_mem 8 19) inputClause9573 (by decide) v hb
mask_input "9573|39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816|2663265347316731026309508216199544711162924299998300720017750922150579995486117230536911880338085273375881915186928418816"
def inputClause9574 : CNF.NClause := [(373,true),(381,false),(384,true),(387,true),(395,true),(400,true)]
theorem inputList9574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 19) (closed_mem 8 19) inputClause9574 (by decide) v hb
mask_input "9574|4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352|2663299824072152871478818960359632336825003744770162377283585376907308710492667290596196867821058297677067620986419937280"
def inputClause9583 : CNF.NClause := [(376,true),(377,true),(383,true),(389,true),(395,false),(398,true)]
theorem inputList9583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 21) (closed_mem 8 21) inputClause9583 (by decide) v hb
mask_input "9583|80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168|646843496465370081986182130699008809589065818011790580991326298689863222466335967735219154484250892049907174105543606272"
def inputClause9585 : CNF.NClause := [(376,true),(377,true),(383,false),(389,true),(395,true),(398,true)]
theorem inputList9585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 21) (closed_mem 8 21) inputClause9585 (by decide) v hb
mask_input "9585|19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408|727519104152487778173323465304052858854966584168068583043950429435056337793476506462089864641127756824458744915696812032"
def inputClause9589 : CNF.NClause := [(374,true),(377,true),(385,true),(388,true),(396,false),(400,true)]
theorem inputList9589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) inputClause9589 (by decide) v hb
mask_input "9589|161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336|2582959460505138775780092646396065339546677936844737822695897280836221543262142151720353449455925265741891565553576837120"
def inputClause9593 : CNF.NClause := [(374,false),(377,true),(385,true),(388,true),(396,true),(400,true)]
theorem inputList9593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) inputClause9593 (by decide) v hb
mask_input "9593|38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784|2744350039407048886467103988905003483895786692373381410933900728951756742054482058906961546326689490670585083326650908672"
def inputClause9597 : CNF.NClause := [(375,true),(377,true),(384,false),(391,true),(393,true),(399,true)]
theorem inputList9597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 23) (closed_mem 8 23) inputClause9597 (by decide) v hb
mask_input "9597|39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816|1316342607794363523188654229078098827965082494779538455421944202731593848779305486883575184135639157088572132652396576768"
def inputClause9599 : CNF.NClause := [(375,false),(377,true),(384,true),(391,true),(393,true),(399,true)]
theorem inputList9599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 23) (closed_mem 8 23) inputClause9599 (by decide) v hb
mask_input "9599|76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568|1316381932843516565334899296635698775985891861472443158240786627688487539333651649138697122983405262932112078329941590016"
def inputClause9603 : CNF.NClause := [(373,true),(377,true),(386,false),(390,true),(394,true),(401,true)]
theorem inputList9603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 24) (closed_mem 8 24) inputClause9603 (by decide) v hb
mask_input "9603|157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264|5207369465982928620109908588435605831749570122431767922804304930485284448782629027965339698774167762145432614238341300224"
def inputClause9605 : CNF.NClause := [(373,false),(377,true),(386,true),(390,true),(394,true),(401,true)]
theorem inputList9605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 24) (closed_mem 8 24) inputClause9605 (by decide) v hb
mask_input "9605|19239260838083241802870625048898248928261591440656956380834127638791856333738872368854622194768025215237611323392|5207527054768453359943515901725381357306541513127258343934020342824773792877858683068912986984565107039970625512691204096"
def inputClause9609 : CNF.NClause := [(372,true),(373,true),(374,false),(375,true),(376,true),(402,true)]
theorem inputList9609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) inputClause9609 (by decide) v hb
mask_input "9609|38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784|10328999772077655672747441026765485657445183702848378500191548567423313611757425283993358392657950955111953093598742839296"
def inputClause9610 : CNF.NClause := [(372,true),(373,false),(374,true),(375,true),(376,true),(402,true)]
theorem inputList9610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) inputClause9610 (by decide) v hb
mask_input "9610|19239260838083241802870625048898248928261591440656956380834127638791856333738872368854622194768025215237611323392|10328999791316916510830682829636110706343432631109969940848504948257441250549281617732230761512573149879978308836354162688"
def inputClause9612 : CNF.NClause := [(372,true),(381,true),(385,true),(389,true),(393,true),(401,false)]
theorem inputList9612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) inputClause9612 (by decide) v hb
mask_input "9612|5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343945494986752|21518430253636354001426792210003455538423636739878662390011452152457514198387081014594800585760121938348127330011971584"
def inputClause9613 : CNF.NClause := [(372,true),(381,true),(385,true),(389,true),(393,false),(401,true)]
theorem inputList9613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) inputClause9613 (by decide) v hb
mask_input "9613|20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792|5165844359254899559956578267684753673929634395891847379357340639010778948685062898440841402823534708002061477744469868544"
def inputClause9614 : CNF.NClause := [(372,true),(381,true),(385,true),(389,false),(393,true),(401,true)]
theorem inputList9614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) inputClause9614 (by decide) v hb
mask_input "9614|1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112|5184757322229168909978472206932822608556072670741670793757955819844816895135381559534320250625879467509648659179817140224"
def inputClause9615 : CNF.NClause := [(372,true),(381,true),(385,false),(389,true),(393,true),(401,true)]
theorem inputList9615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) inputClause9615 (by decide) v hb
mask_input "9615|78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632|5185939382415060744354840578135826916970225062919784757157994268646944266788526475852662678613526014978872858019526344704"
end Percolation.MaskChain
