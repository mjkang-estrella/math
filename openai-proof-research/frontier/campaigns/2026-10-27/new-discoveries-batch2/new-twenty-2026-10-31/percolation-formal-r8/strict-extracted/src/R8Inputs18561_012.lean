import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9616 : CNF.NClause := [(372,true),(381,false),(385,true),(389,true),(393,true),(401,true)]
theorem inputList9616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) inputClause9616 (by decide) v hb
mask_input "9616|4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352|5186013261176678984003363601336014686246109587430916879870496671697077227516848033122559080362753924195699370447008169984"
def inputClause9619 : CNF.NClause := [(372,true),(379,true),(386,true),(388,true),(395,false),(399,true)]
theorem inputList9619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) inputClause9619 (by decide) v hb
mask_input "9619|80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168|1291914220099706240781301451958824463378010364072668987722375207939641427518584067684318753088298176568394101372110241792"
def inputClause9621 : CNF.NClause := [(372,true),(379,true),(386,false),(388,true),(395,true),(399,true)]
theorem inputList9621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) inputClause9621 (by decide) v hb
mask_input "9621|157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264|1372451920765136556291199809923518009995593351141500360711661519657919682819524366174049513313282944138202848984297373696"
def inputClause9622 : CNF.NClause := [(372,true),(379,false),(386,true),(388,true),(395,true),(399,true)]
theorem inputList9622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) inputClause9622 (by decide) v hb
mask_input "9622|1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088|1372608297477228496880573542363915454962882261356730020453124939447367783027804995728663563682482018647152300289133903872"
def inputClause9631 : CNF.NClause := [(372,true),(378,true),(384,true),(390,true),(396,false),(398,true)]
theorem inputList9631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) inputClause9631 (by decide) v hb
mask_input "9631|161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336|648124225200470026268136523902576392672846799761607953592163855315586138154688463860505253401823307336447719034924826624"
def inputClause9633 : CNF.NClause := [(372,true),(378,true),(384,false),(390,true),(396,true),(398,true)]
theorem inputList9633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) inputClause9633 (by decide) v hb
mask_input "9633|39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816|809475440574705418642419193112664491204648332074163957697412116805972368808969541314246673715577036885550860655231238144"
def inputClause9637 : CNF.NClause := [(372,true),(377,true),(382,true),(387,true),(392,false),(397,true)]
theorem inputList9637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) inputClause9637 (by decide) v hb
mask_input "9637|10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896|323106618759787656533980945946515975926212448268893049878623276751272020022349508007643922957886243155940602598100303872"
def inputClause9639 : CNF.NClause := [(372,true),(377,true),(382,false),(387,true),(392,true),(397,true)]
theorem inputList9639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) inputClause9639 (by decide) v hb
mask_input "9639|9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704|333183681844515544592521310452127705156861591587314587863951052789407863365409919621513121552573060331076897706621272064"
def inputClause9640 : CNF.NClause := [(372,true),(377,false),(382,true),(387,true),(392,true),(397,true)]
theorem inputList9640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) inputClause9640 (by decide) v hb
mask_input "9640|307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272|333193224517891233880455534282151958688330009336669153714315946516716704126151454102208073445181665271583655561837674496"
def inputClause9643 : CNF.NClause := [(428,true),(429,true),(430,true),(431,true),(432,false),(433,true)]
theorem inputList9643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) inputClause9643 (by decide) v hb
mask_input "9643|11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296|32578868905919574600046366663681233515378135635665844758253135072221800366716101070719699271723640042644346728796491968990446354432"
def inputClause9655 : CNF.NClause := [(405,true),(410,true),(415,true),(420,true),(425,false),(428,true)]
theorem inputList9655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) inputClause9655 (by decide) v hb
mask_input "9655|86645927941275464361825443254471365732388658605494267974077486894206915868925800719999200190754361815543475342543861619655442432|695962450798244984752047112947546985911883742394112495322907800841174923937477434669060729656425315713094024333694194844073721856"
def inputClause9657 : CNF.NClause := [(405,true),(410,true),(415,false),(420,true),(425,true),(428,true)]
theorem inputList9657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) inputClause9657 (by decide) v hb
mask_input "9657|84615164005151820665845159428194693098035799419427996068435045795123941278247852265624218936283556460491675139202989862944768|782523763575515297293206711042590156951174365200187335300916852689586715865124987536794305628243393972177008001098853473866219520"
def inputClause9658 : CNF.NClause := [(405,true),(410,false),(415,true),(420,true),(425,true),(428,true)]
theorem inputList9658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) inputClause9658 (by decide) v hb
mask_input "9658|2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024|782605734515645288119476748540786220560113087380874906172108149140200742183238290143676629090337918667498109311389956370295947264"
def inputClause9661 : CNF.NClause := [(406,true),(411,true),(416,true),(421,true),(426,false),(428,true)]
theorem inputList9661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 3) (closed_mem 9 3) inputClause9661 (by decide) v hb
mask_input "9661|173291855882550928723650886508942731464777317210988535948154973788413831737851601439998400381508723631086950685087723239310884864|698757478066286254609490679859323045964658215944270846853195706528694520923548463578127857786815736901840245927037496730903904256"
def inputClause9670 : CNF.NClause := [(404,true),(409,false),(414,true),(419,true),(424,true),(428,true)]
theorem inputList9670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) inputClause9670 (by decide) v hb
mask_input "9670|1322111937580497197903830616065542079656809365928562438569297590548811582472622691650378420879430569695182424050046716608512|737886579022924501507040147288278573209611178112414524982364022146928034567322347951835115308186406595922956025870424663769743360"
def inputClause9671 : CNF.NClause := [(404,false),(409,true),(414,true),(419,true),(424,true),(428,true)]
theorem inputList9671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) inputClause9671 (by decide) v hb
mask_input "9671|41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016|737887859818864032613700616624187886703500845646487768277226386153968878728542868305067651612281633544287348233843723146526457856"
def inputClause9673 : CNF.NClause := [(423,true),(424,true),(425,true),(426,true),(427,false),(433,true)]
theorem inputList9673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) inputClause9673 (by decide) v hb
mask_input "9673|346583711765101857447301773017885462929554634421977071896309947576827663475703202879996800763017447262173901370175446478621769728|22506279782746301867984158885348937248987954072777136106266627220770246396953476737019792249548445481587417720225768055705501171712"
def inputClause9674 : CNF.NClause := [(423,true),(424,true),(425,true),(426,false),(427,true),(433,true)]
theorem inputList9674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) inputClause9674 (by decide) v hb
mask_input "9674|173291855882550928723650886508942731464777317210988535948154973788413831737851601439998400381508723631086950685087723239310884864|22679571638628852796707809771857879980452731389988124642214782194558660228691328338459790649929954205218504670910855778944812056576"
def inputClause9680 : CNF.NClause := [(407,true),(411,true),(415,true),(419,false),(423,true),(432,true)]
theorem inputList9680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) inputClause9680 (by decide) v hb
mask_input "9680|1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288|11112430492608318173337870033825499128425782043393864492061870048742591916580237698838602562791471923979832408881691668409219022848"
def inputClause9681 : CNF.NClause := [(407,true),(411,true),(415,false),(419,true),(423,true),(432,true)]
theorem inputList9681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) inputClause9681 (by decide) v hb
mask_input "9681|84615164005151820665845159428194693098035799419427996068435045795123941278247852265624218936283556460491675139202989862944768|11113699720068395450647857711216922048822252580385155912002896574429518775699411416622586926075516177326739784008779713257163194368"
def inputClause9682 : CNF.NClause := [(407,true),(411,false),(415,true),(419,true),(423,true),(432,true)]
theorem inputList9682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) inputClause9682 (by decide) v hb
mask_input "9682|5288447750321988791615322464262168318627237463714249754277190362195246329890490766601513683517722278780729696200186866434048|11113779046784650280479731941053885981347031988947111625749210732284951704394359773984085948780768943160921494954222716060159705088"
def inputClause9708 : CNF.NClause := [(407,true),(410,true),(413,true),(421,true),(424,true),(431,false)]
theorem inputList9708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) inputClause9708 (by decide) v hb
mask_input "9708|5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648|48762463009828292777388556739383339367422357236518721999922476059018905987650888269122169513480378129140141959419835513634291712"
def inputClause9709 : CNF.NClause := [(407,true),(410,true),(413,true),(421,true),(424,false),(431,true)]
theorem inputList9709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) inputClause9709 (by decide) v hb
mask_input "9709|43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216|5550778887280820279753304203398315063374102178685404738353842893841158063664439233989071381626382353416150826210955048361754886144"
def inputClause9712 : CNF.NClause := [(407,true),(410,false),(413,true),(421,true),(424,true),(431,true)]
theorem inputList9712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) inputClause9712 (by decide) v hb
mask_input "9712|2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024|5594099207027582850939821117364318615156137194369420015216004498693080423975737189103687680964917775462783173517378879078149390336"
def inputClause9716 : CNF.NClause := [(405,true),(409,true),(413,true),(422,false),(426,true),(432,true)]
theorem inputList9716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) inputClause9716 (by decide) v hb
mask_input "9716|10830740992659433045228180406808920716548582325686783496759685861775864483615725089999900023844295226942934417817982702456930304|11263993190900745334270746857191164163522259763024060992726681384887037802057980032724572309379873291304747218580812364477309648896"
def inputClause9718 : CNF.NClause := [(405,true),(409,false),(413,true),(422,true),(426,true),(432,true)]
theorem inputList9718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) inputClause9718 (by decide) v hb
mask_input "9718|1322111937580497197903830616065542079656809365928562438569297590548811582472622691650378420879430569695182424050046716608512|11274822609781467186818777133767357018696728688540381847661002501451223117730013285191880559025296707101120457816206297133049970688"
def inputClause9726 : CNF.NClause := [(404,true),(411,true),(413,true),(420,true),(427,true),(430,false)]
theorem inputList9726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) inputClause9726 (by decide) v hb
mask_input "9726|2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824|349317880568016375043104329226615755998474905466010024286847460284632310478618538875788897411721762162508841597561694652528066560"
def inputClause9727 : CNF.NClause := [(404,true),(411,true),(413,true),(420,true),(427,false),(430,true)]
theorem inputList9727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) inputClause9727 (by decide) v hb
mask_input "9727|346583711765101857447301773017885462929554634421977071896309947576827663475703202879996800763017447262173901370175446478621769728|2775403862923729377174216740351813996505357346419849527561017093322425954808540959035766502752843892997726151188789820002880454656"
def inputClause9728 : CNF.NClause := [(404,true),(411,true),(413,true),(420,false),(427,true),(430,true)]
theorem inputList9728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) inputClause9728 (by decide) v hb
mask_input "9728|2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576|3119279889440666376360211468267997229255774835260404903583137119433809652163340230643263328509900266453164318954510770805887991808"
def inputClause9734 : CNF.NClause := [(418,true),(419,true),(420,true),(421,false),(422,true),(433,true)]
theorem inputList9734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) inputClause9734 (by decide) v hb
mask_input "9734|5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152|22196926743143466811629828982479457451021535190099707352640428693343273267640202589136670105117392799167860155916841924766575099904"
def inputClause9736 : CNF.NClause := [(418,true),(419,false),(420,true),(421,true),(422,true),(433,true)]
theorem inputList9736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) inputClause9736 (by decide) v hb
mask_input "9736|1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288|22200988271015714099021789550132010796290240908471839896451713575541439216821558486045420067626334409877963756323523668279996448768"
def inputClause9742 : CNF.NClause := [(407,true),(409,false),(416,true),(418,true),(425,true),(430,true)]
theorem inputList9742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 16) (closed_mem 9 16) inputClause9742 (by decide) v hb
mask_input "9742|1322111937580497197903830616065542079656809365928562438569297590548811582472622691650378420879430569695182424050046716608512|2860162104230126237271197554949491032485326006177846605245851060291177100290229520438302761078861995335182026850945475858938200064"
def inputClause9744 : CNF.NClause := [(405,true),(411,true),(417,true),(418,true),(424,true),(429,false)]
theorem inputList9744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) inputClause9744 (by decide) v hb
mask_input "9744|1386334847060407429789207092071541851718218537687908287585239790307310653902812811519987203052069789048695605480701785914487078912|44343717018445974798769347852251785448069364683829354724766651768106549776855669616871920384947406271987024451540070002969280512"
def inputClause9747 : CNF.NClause := [(405,true),(411,true),(417,false),(418,true),(424,true),(429,true)]
theorem inputList9747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) inputClause9747 (by decide) v hb
mask_input "9747|338460656020607282663380637712778772392143197677711984273740183180495765112991409062496875745134225841966700556811959451779072|1430340103422832797305313059286080858393895759174059930325732701892236707914555489727796626561272061094840663231685043958004580352"
def inputClause9750 : CNF.NClause := [(406,true),(410,true),(414,true),(418,true),(427,true),(432,false)]
theorem inputList9750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) inputClause9750 (by decide) v hb
mask_input "9750|11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296|347305750147013006479507002513084257097807209436944808058073605223466133201181063947474363678120226282048682871509778241729593344"
def inputClause9751 : CNF.NClause := [(406,true),(410,true),(414,true),(418,true),(427,false),(432,true)]
theorem inputList9751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) inputClause9751 (by decide) v hb
mask_input "9751|346583711765101857447301773017885462929554634421977071896309947576827663475703202879996800763017447262173901370175446478621769728|11091400814865170587345861966067533607914000876518234036843681980105123700947980353227375187331661091409439625346948619079004454912"
def inputClause9752 : CNF.NClause := [(406,true),(410,true),(414,true),(418,false),(427,true),(432,true)]
theorem inputList9752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) inputClause9752 (by decide) v hb
mask_input "9752|676921312041214565326761275425557544784286395355423968547480366360991530225982818124993751490268451683933401113623918903558144|11437307605318231230227836977809993513298771224544855684771444447315590372893457573289246994343188270219929593316010441638722666496"
def inputClause9754 : CNF.NClause := [(406,true),(410,false),(414,true),(418,true),(427,true),(432,true)]
theorem inputList9754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) inputClause9754 (by decide) v hb
mask_input "9754|2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024|11437981882406397283798767931424186939759396197321479251615114789086770266800518610861988687337836779810474136352275965464193007616"
def inputClause9769 : CNF.NClause := [(407,true),(408,true),(414,true),(420,true),(426,false),(429,true)]
theorem inputList9769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) inputClause9769 (by decide) v hb
mask_input "9769|173291855882550928723650886508942731464777317210988535948154973788413831737851601439998400381508723631086950685087723239310884864|1389085831474528049333745487625920228400464443776064143879292856268845093603042721185638727951314664206588856309543920620070240256"
def inputClause9771 : CNF.NClause := [(407,true),(408,true),(414,false),(420,true),(426,true),(429,true)]
theorem inputList9771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) inputClause9771 (by decide) v hb
mask_input "9771|42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384|1562335379775076402147063451555148862518692743087342965829413612534361363370255198699504316223355246059445561157062042364449652736"
end Percolation.MaskChain
