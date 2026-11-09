import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9628 : CNF.NClause := [(372,true),(380,false),(383,true),(391,true),(394,true),(400,true)]
theorem inputList9628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 28) (closed_mem 8 28) inputClause9628 (by decide) v hb
mask_input "9628|2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176|2627660699847883645989691667153739913689184656469230660443947955106104635754419896728736479566203794095945418350381760512"
def inputClause9632 : CNF.NClause := [(372,true),(378,true),(384,true),(390,false),(396,true),(398,true)]
theorem inputList9632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) inputClause9632 (by decide) v hb
mask_input "9632|2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224|806993114184332566452045613586355443534928308500124634557331374321504888337365217045727574941519287200180043091841908736"
def inputClause9634 : CNF.NClause := [(372,true),(378,false),(384,true),(390,true),(396,true),(398,true)]
theorem inputList9634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) inputClause9634 (by decide) v hb
mask_input "9634|615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544|809514226924554994457893780292763070074487707442508322121475878407292173191338358880942284633921689224384779679659196416"
def inputClause9638 : CNF.NClause := [(372,true),(377,true),(382,true),(387,false),(392,true),(397,true)]
theorem inputList9638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) inputClause9638 (by decide) v hb
mask_input "9638|315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528|332878316296493487378626147891351592149872223607968480652274453515524959021680816239274660989097702234860646339696394240"
def inputClause9645 : CNF.NClause := [(428,true),(429,true),(430,false),(431,true),(432,true),(433,true)]
theorem inputList9645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) inputClause9645 (by decide) v hb
mask_input "9645|2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824|40896877988282019178781609216110484625687446861793294483764573814065664290132977939839622490036058776936520361680702684477368827904"
def inputClause9652 : CNF.NClause := [(407,true),(412,false),(417,true),(422,true),(427,true),(428,true)]
theorem inputList9652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 1) (closed_mem 9 1) inputClause9652 (by decide) v hb
mask_input "9652|10576895500643977583230644928524336637254474927428499508554380724390492659780981533203027367035444557561459392400373732868096|1050920667471970007794096356055832104663124542991637193310572911099836987878733943294725711783246991096949029024507146609453170688"
def inputClause9665 : CNF.NClause := [(406,false),(411,true),(416,true),(421,true),(426,true),(428,true)]
theorem inputList9665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 3) (closed_mem 9 3) inputClause9665 (by decide) v hb
mask_input "9665|165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064|872049168684844985770991828389438769236675576054088641731045859154909534059952255940289801871021850604105984714322213714375213056"
def inputClause9667 : CNF.NClause := [(404,true),(409,true),(414,true),(419,true),(424,false),(428,true)]
theorem inputList9667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) inputClause9667 (by decide) v hb
mask_input "9667|43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216|694564937164224349823325329491658955885496505619033319557763847997415125444441920214527165591230105118720913537022543900658630656"
def inputClause9668 : CNF.NClause := [(404,true),(409,true),(414,true),(419,false),(424,true),(428,true)]
theorem inputList9668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) inputClause9668 (by decide) v hb
mask_input "9668|1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288|736534058510779652873584528568043523662122262131069605607707630711796600318452854938276778183626749123124784406067226872679235584"
def inputClause9669 : CNF.NClause := [(404,true),(409,true),(414,false),(419,true),(424,true),(428,true)]
theorem inputList9669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 4) (closed_mem 9 4) inputClause9669 (by decide) v hb
mask_input "9669|42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384|737845593552859506093905128539180541405141817022070739546768373921621021408265696648393953577139144248262405370724873215554879488"
def inputClause9688 : CNF.NClause := [(405,true),(412,false),(414,true),(421,true),(423,true),(430,true)]
theorem inputList9688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 7) (closed_mem 9 7) inputClause9688 (by decide) v hb
mask_input "9688|10576895500643977583230644928524336637254474927428499508554380724390492659780981533203027367035444557561459392400373732868096|2799788936816462116882892426729233606670737527640328618445565423373057940286027964230025196421869762907389398792419633207967744000"
def inputClause9691 : CNF.NClause := [(406,true),(409,true),(417,true),(420,true),(423,false),(431,true)]
theorem inputList9691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) inputClause9691 (by decide) v hb
mask_input "9691|21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608|5548387021521744962760146435835025489559243053441269227832166213337656444910298450462039390765708853586751029308045507595570511872"
def inputClause9694 : CNF.NClause := [(406,true),(409,false),(417,true),(420,true),(423,true),(431,true)]
theorem inputList9694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) inputClause9694 (by decide) v hb
mask_input "9694|1322111937580497197903830616065542079656809365928562438569297590548811582472622691650378420879430569695182424050046716608512|5570047181395126248353404892818027265450260561283276866263247015763617625065947428019347540434976564610067202961257422953767763968"
def inputClause9695 : CNF.NClause := [(406,false),(409,true),(417,true),(420,true),(423,true),(431,true)]
theorem inputList9695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) inputClause9695 (by decide) v hb
mask_input "9695|165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064|5570048338243071631288453058669816322799580260991472053755380763899009355276082091564202734516094834111815686245878466744644796416"
def inputClause9697 : CNF.NClause := [(404,true),(410,true),(416,true),(422,true),(423,false),(429,true)]
theorem inputList9697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 9) (closed_mem 9 9) inputClause9697 (by decide) v hb
mask_input "9697|21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608|1397337503920950376860700204953146044953312494506458469466589690146407568542511929829360766344954062731904216588097026254063009792"
def inputClause9700 : CNF.NClause := [(404,true),(410,false),(416,true),(422,true),(423,true),(429,true)]
theorem inputList9700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 9) (closed_mem 9 9) inputClause9700 (by decide) v hb
mask_input "9700|2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024|1418996341682394081956760758105531755302250345539100179335231923274778199886578434763977265635800894324650695058884891565543653376"
def inputClause9703 : CNF.NClause := [(413,true),(414,true),(415,true),(416,true),(417,false),(433,true)]
theorem inputList9703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) inputClause9703 (by decide) v hb
mask_input "9703|338460656020607282663380637712778772392143197677711984273740183180495765112991409062496875745134225841966700556811959451779072|22181674859831538195954810392492525357590614237254355456349093276338702177224798413765791339654127688115856531473000585843779305472"
def inputClause9704 : CNF.NClause := [(413,true),(414,true),(415,true),(416,false),(417,true),(433,true)]
theorem inputList9704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) inputClause9704 (by decide) v hb
mask_input "9704|169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536|22181844090159548499596142082811381746976810308853194312341230146430292425107354909470322588092000255228777514823278991823505195008"
def inputClause9705 : CNF.NClause := [(413,true),(414,true),(415,false),(416,true),(417,true),(433,true)]
theorem inputList9705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) inputClause9705 (by decide) v hb
mask_input "9705|84615164005151820665845159428194693098035799419427996068435045795123941278247852265624218936283556460491675139202989862944768|22181928705323553651416807927970809941669908344652613740337298581476087549048633157322588212310936538785238006498418194813368139776"
def inputClause9706 : CNF.NClause := [(413,true),(414,false),(415,true),(416,true),(417,true),(433,true)]
theorem inputList9706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) inputClause9706 (by decide) v hb
mask_input "9706|42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384|22181971012905556227327140850550524039016457362552323454335332798998985111019272281248721024420404680563468252335987796308299612160"
def inputClause9715 : CNF.NClause := [(405,true),(409,true),(413,true),(422,true),(426,false),(432,true)]
theorem inputList9715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) inputClause9715 (by decide) v hb
mask_input "9715|173291855882550928723650886508942731464777317210988535948154973788413831737851601439998400381508723631086950685087723239310884864|11101532076010853838592324151089030352774031028138759240275286096960399834803744156374573809022208862900603202313542623940455694336"
def inputClause9724 : CNF.NClause := [(406,true),(412,false),(413,true),(419,true),(425,true),(429,true)]
theorem inputList9724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 13) (closed_mem 9 13) inputClause9724 (by decide) v hb
mask_input "9724|10576895500643977583230644928524336637254474927428499508554380724390492659780981533203027367035444557561459392400373732868096|1474355936680758808799002257145548389406210235135139001565734167857887152418957948917139253097841368585543282442060702375254949888"
def inputClause9735 : CNF.NClause := [(418,true),(419,true),(420,false),(421,true),(422,true),(433,true)]
theorem inputList9735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) inputClause9735 (by decide) v hb
mask_input "9735|2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576|22199634428391631669891136027581159681200672335681129048514618614808717233761106520409170080123353872974595889521296420442189332480"
def inputClause9737 : CNF.NClause := [(418,false),(419,true),(420,true),(421,true),(422,true),(433,true)]
theorem inputList9737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 15) (closed_mem 9 15) inputClause9737 (by decide) v hb
mask_input "9737|676921312041214565326761275425557544784286395355423968547480366360991530225982818124993751490268451683933401113623918903558144|22201665192327755313587116311407436353835025194867195320420261055907800208351784468863545061377824678329647689724637292198900006912"
def inputClause9746 : CNF.NClause := [(405,true),(411,true),(417,true),(418,false),(424,true),(429,true)]
theorem inputList9746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) inputClause9746 (by decide) v hb
mask_input "9746|676921312041214565326761275425557544784286395355423968547480366360991530225982818124993751490268451683933401113623918903558144|1430001642766812190022649678648368079621503615976382218341458961709056212149442498318734129685526926868998696531128231998552801280"
def inputClause9755 : CNF.NClause := [(406,false),(410,true),(414,true),(418,true),(427,true),(432,true)]
theorem inputList9755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) inputClause9755 (by decide) v hb
mask_input "9755|165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064|11437984361366280247231014001106592062650795553839040367669687106519752545822235747029535531797375928742792314819321059301786648576"
def inputClause9770 : CNF.NClause := [(407,true),(408,true),(414,true),(420,false),(426,true),(429,true)]
theorem inputList9770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) inputClause9770 (by decide) v hb
mask_input "9770|2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576|1559670002108914119796089329033160729686104615405630983953257908591814959219990391353137153326862314030940073390177148183766892544"
def inputClause9774 : CNF.NClause := [(405,true),(408,true),(416,true),(419,true),(427,true),(431,false)]
theorem inputList9774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) inputClause9774 (by decide) v hb
mask_input "9774|5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648|348107528405159479248960806792314504272739085766795110641913473631034578125226805071042090041732295958158205062794628447432867840"
def inputClause9777 : CNF.NClause := [(405,true),(408,true),(416,false),(419,true),(427,true),(431,true)]
theorem inputList9777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) inputClause9777 (by decide) v hb
mask_input "9777|169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536|5893277686318778894764457484759625521759417164919589404990735764768686945853921555446459653812138885040019643635323366125655293952"
def inputClause9787 : CNF.NClause := [(404,true),(408,true),(417,true),(421,true),(425,false),(432,true)]
theorem inputList9787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) inputClause9787 (by decide) v hb
mask_input "9787|86645927941275464361825443254471365732388658605494267974077486894206915868925800719999200190754361815543475342543861619655442432|11096433310007576601758070593823466837695644553543763053963367395511898638285576534694765010567761686426368428320742867213895073792"
def inputClause9788 : CNF.NClause := [(404,true),(408,true),(417,true),(421,false),(425,true),(432,true)]
theorem inputList9788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) inputClause9788 (by decide) v hb
mask_input "9788|5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152|11177663867452522349597281946874533743069758920986413930189065039475217621912694472869764260746593900628440436454377737482322051072"
def inputClause9791 : CNF.NClause := [(404,false),(408,true),(417,true),(421,true),(425,true),(432,true)]
theorem inputList9791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) inputClause9791 (by decide) v hb
mask_input "9791|41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016|11183079196632854016729358602583231451379843222873964636669868677115555849504140383145305096684190395759706600688835977269590622208"
def inputClause9794 : CNF.NClause := [(403,true),(404,true),(405,true),(406,false),(407,true),(433,true)]
theorem inputList9794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 25) (closed_mem 9 25) inputClause9794 (by decide) v hb
mask_input "9794|165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064|22181358028100496444618493969833797276045681479672398481940963005758292065924167435418575060687861628324490671897412217617332043776"
def inputClause9804 : CNF.NClause := [(403,true),(410,true),(417,true),(419,true),(426,true),(430,false)]
theorem inputList9804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) inputClause9804 (by decide) v hb
mask_input "9804|2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824|174986824044528150826632314606092132434992341455755295628188915944772260511762479865423742554238979862538826039945258911982944256"
def inputClause9805 : CNF.NClause := [(403,true),(410,true),(417,true),(419,true),(426,false),(430,true)]
theorem inputList9805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) inputClause9805 (by decide) v hb
mask_input "9805|173291855882550928723650886508942731464777317210988535948154973788413831737851601439998400381508723631086950685087723239310884864|2774364662282792081681395612240233104406652099620583334850513522770979736579536501465399748276869834328843086316261107501646217216"
def inputClause9806 : CNF.NClause := [(403,true),(410,true),(417,true),(419,false),(426,true),(430,true)]
theorem inputList9806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) inputClause9806 (by decide) v hb
mask_input "9806|1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288|2946302675541260581274392976198324720781860844040861022861573535826671585256936137269148161155398021056562170199121582903149985792"
def inputClause9810 : CNF.NClause := [(403,true),(411,true),(414,true),(422,true),(425,true),(431,false)]
theorem inputList9810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) inputClause9810 (by decide) v hb
mask_input "9810|5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648|97524285621686820001446878810812021987899880706000822352413770114517389894691516361628070874913142784098087814853021785890226176"
def inputClause9811 : CNF.NClause := [(403,true),(411,true),(414,true),(422,true),(425,false),(431,true)]
theorem inputList9811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) inputClause9811 (by decide) v hb
mask_input "9811|86645927941275464361825443254471365732388658605494267974077486894206915868925800719999200190754361815543475342543861619655442432|5556217745922041074796449803842508063128385372852139704719295444449553089637016961721577682892437937163337034395116303824183099392"
def inputClause9814 : CNF.NClause := [(403,true),(411,false),(414,true),(422,true),(425,true),(431,true)]
theorem inputList9814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) inputClause9814 (by decide) v hb
mask_input "9814|5288447750321988791615322464262168318627237463714249754277190362195246329890490766601513683517722278780729696200186866434048|5642858385415566217169483631774515166692455404220170258443618654153397810259612871950810281569508781256601729007963965256972107776"
def inputClause9816 : CNF.NClause := [(403,true),(409,true),(415,true),(421,true),(427,true),(429,false)]
theorem inputList9816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) inputClause9816 (by decide) v hb
mask_input "9816|1386334847060407429789207092071541851718218537687908287585239790307310653902812811519987203052069789048695605480701785914487078912|352085040195373330983048329458687559547101612831252162836984897496376120795552762034683582409459584103778206923873066648409735168"
end Percolation.MaskChain
