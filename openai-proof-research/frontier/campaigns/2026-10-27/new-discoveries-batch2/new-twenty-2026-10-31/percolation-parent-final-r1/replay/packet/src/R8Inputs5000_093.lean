import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14573 : CNF.NClause := [(26,true),(28,true),(958,false)]
theorem inputList14573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14573 = (containClause5 26 28) := by decide
  rw [he]
  exact input_contain 26 28 (by decide) v hb
mask_input "14573|2436328502849999770088345596968797077719056714398751881716976614303237172691606525616403766470502564806326229057852167045864792466300773511644496824078163354882819424989118257467697413872513412088199898369804594718421399481348718736436590903867241403206934700776069386770457147497978527744|335544320"
def inputClause14574 : CNF.NClause := [(26,true),(29,true),(959,false)]
theorem inputList14574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14574 = (containClause5 26 29) := by decide
  rw [he]
  exact input_contain 26 29 (by decide) v hb
mask_input "14574|4872657005699999540176691193937594155438113428797503763433953228606474345383213051232807532941005129612652458115704334091729584932601547023288993648156326709765638849978236514935394827745026824176399796739609189436842798962697437472873181807734482806413869401552138773540914294995957055488|603979776"
def inputClause14579 : CNF.NClause := [(27,true),(3,true),(964,false)]
theorem inputList14579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14579 = (containClause5 27 3) := by decide
  rw [he]
  exact input_contain 27 3 (by decide) v hb
mask_input "14579|155925024182399985285654118206003012974019629721520120429886503315407179052262817639449841054112164147604878659702538690935346717843249504745247796741002454712500443199303568477932634487840858373644793495667494061978969566806317999131941817847503449805243820849668440753309257439870625775616|134217736"
def inputClause14582 : CNF.NClause := [(27,true),(6,true),(967,false)]
theorem inputList14582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14582 = (containClause5 27 6) := by decide
  rw [he]
  exact input_contain 27 6 (by decide) v hb
mask_input "14582|1247400193459199882285232945648024103792157037772160963439092026523257432418102541115598728432897313180839029277620309527482773742745996037961982373928019637700003545594428547823461075902726866989158347965339952495831756534450543993055534542780027598441950566797347526026474059518965006204928|134217792"
def inputClause14583 : CNF.NClause := [(27,true),(7,true),(968,false)]
theorem inputList14583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14583 = (containClause5 27 7) := by decide
  rw [he]
  exact input_contain 27 7 (by decide) v hb
mask_input "14583|2494800386918399764570465891296048207584314075544321926878184053046514864836205082231197456865794626361678058555240619054965547485491992075923964747856039275400007091188857095646922151805453733978316695930679904991663513068901087986111069085560055196883901133594695052052948119037930012409856|134217856"
def inputClause14585 : CNF.NClause := [(27,true),(9,true),(970,false)]
theorem inputList14585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14585 = (containClause5 27 9) := by decide
  rw [he]
  exact input_contain 27 9 (by decide) v hb
mask_input "14585|9979201547673599058281863565184192830337256302177287707512736212186059459344820328924789827463178505446712234220962476219862189941967968303695858991424157101600028364755428382587688607221814935913266783722719619966654052275604351944444276342240220787535604534378780208211792476151720049639424|134218240"
def inputClause14588 : CNF.NClause := [(27,true),(12,true),(973,false)]
theorem inputList14588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14588 = (containClause5 27 12) := by decide
  rw [he]
  exact input_contain 27 12 (by decide) v hb
mask_input "14588|79833612381388792466254908521473542642698050417418301660101889697488475674758562631398318619705428043573697873767699809758897519535743746429566871931393256812800226918043427060701508857774519487306134269781756959733232418204834815555554210737921766300284836275030241665694339809213760397115392|134221824"
def inputClause14589 : CNF.NClause := [(27,true),(13,true),(974,false)]
theorem inputList14589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14589 = (containClause5 27 13) := by decide
  rw [he]
  exact input_contain 27 13 (by decide) v hb
mask_input "14589|159667224762777584932509817042947085285396100834836603320203779394976951349517125262796637239410856087147395747535399619517795039071487492859133743862786513625600453836086854121403017715549038974612268539563513919466464836409669631111108421475843532600569672550060483331388679618427520794230784|134225920"
def inputClause14591 : CNF.NClause := [(27,true),(15,true),(976,false)]
theorem inputList14591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14591 = (containClause5 27 15) := by decide
  rw [he]
  exact input_contain 27 15 (by decide) v hb
mask_input "14591|638668899051110339730039268171788341141584403339346413280815117579907805398068501051186548957643424348589582990141598478071180156285949971436534975451146054502401815344347416485612070862196155898449074158254055677865859345638678524444433685903374130402278690200241933325554718473710083176923136|134250496"
def inputClause14592 : CNF.NClause := [(27,true),(16,true),(977,false)]
theorem inputList14592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14592 = (containClause5 27 16) := by decide
  rw [he]
  exact input_contain 27 16 (by decide) v hb
mask_input "14592|1277337798102220679460078536343576682283168806678692826561630235159815610796137002102373097915286848697179165980283196956142360312571899942873069950902292109004803630688694832971224141724392311796898148316508111355731718691277357048888867371806748260804557380400483866651109436947420166353846272|134283264"
def inputClause14593 : CNF.NClause := [(27,true),(17,true),(978,false)]
theorem inputList14593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14593 = (containClause5 27 17) := by decide
  rw [he]
  exact input_contain 27 17 (by decide) v hb
mask_input "14593|2554675596204441358920157072687153364566337613357385653123260470319631221592274004204746195830573697394358331960566393912284720625143799885746139901804584218009607261377389665942448283448784623593796296633016222711463437382554714097777734743613496521609114760800967733302218873894840332707692544|134348800"
def inputClause14594 : CNF.NClause := [(27,true),(18,true),(979,false)]
theorem inputList14594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14594 = (containClause5 27 18) := by decide
  rw [he]
  exact input_contain 27 18 (by decide) v hb
mask_input "14594|5109351192408882717840314145374306729132675226714771306246520940639262443184548008409492391661147394788716663921132787824569441250287599771492279803609168436019214522754779331884896566897569247187592593266032445422926874765109428195555469487226993043218229521601935466604437747789680665415385088|134479872"
def inputClause14595 : CNF.NClause := [(27,true),(19,true),(980,false)]
theorem inputList14595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14595 = (containClause5 27 19) := by decide
  rw [he]
  exact input_contain 27 19 (by decide) v hb
mask_input "14595|10218702384817765435680628290748613458265350453429542612493041881278524886369096016818984783322294789577433327842265575649138882500575199542984559607218336872038429045509558663769793133795138494375185186532064890845853749530218856391110938974453986086436459043203870933208875495579361330830770176|134742016"
def inputClause14596 : CNF.NClause := [(27,true),(20,true),(981,false)]
theorem inputList14596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14596 = (containClause5 27 20) := by decide
  rw [he]
  exact input_contain 27 20 (by decide) v hb
mask_input "14596|20437404769635530871361256581497226916530700906859085224986083762557049772738192033637969566644589579154866655684531151298277765001150399085969119214436673744076858091019117327539586267590276988750370373064129781691707499060437712782221877948907972172872918086407741866417750991158722661661540352|135266304"
def inputClause14597 : CNF.NClause := [(27,true),(21,true),(982,false)]
theorem inputList14597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14597
  have he : decodeClause inputClause14597 = containClause5 27 21 := by decide
  rw [he]
  exact input_contain 27 21 (by decide) v hb
mask_input "14597|40874809539271061742722513162994453833061401813718170449972167525114099545476384067275939133289179158309733311369062302596555530002300798171938238428873347488153716182038234655079172535180553977500740746128259563383414998120875425564443755897815944345745836172815483732835501982317445323323080704|136314880"
def inputClause14598 : CNF.NClause := [(27,true),(22,true),(983,false)]
theorem inputList14598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14598 = (containClause5 27 22) := by decide
  rw [he]
  exact input_contain 27 22 (by decide) v hb
mask_input "14598|81749619078542123485445026325988907666122803627436340899944335050228199090952768134551878266578358316619466622738124605193111060004601596343876476857746694976307432364076469310158345070361107955001481492256519126766829996241750851128887511795631888691491672345630967465671003964634890646646161408|138412032"
def inputClause14599 : CNF.NClause := [(27,true),(23,true),(984,false)]
theorem inputList14599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14599 = (containClause5 27 23) := by decide
  rw [he]
  exact input_contain 27 23 (by decide) v hb
mask_input "14599|163499238157084246970890052651977815332245607254872681799888670100456398181905536269103756533156716633238933245476249210386222120009203192687752953715493389952614864728152938620316690140722215910002962984513038253533659992483501702257775023591263777382983344691261934931342007929269781293292322816|142606336"
def inputClause14600 : CNF.NClause := [(27,true),(24,true),(985,false)]
theorem inputList14600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14600 = (containClause5 27 24) := by decide
  rw [he]
  exact input_contain 27 24 (by decide) v hb
mask_input "14600|326998476314168493941780105303955630664491214509745363599777340200912796363811072538207513066313433266477866490952498420772444240018406385375505907430986779905229729456305877240633380281444431820005925969026076507067319984967003404515550047182527554765966689382523869862684015858539562586584645632|150994944"
def inputClause14602 : CNF.NClause := [(27,true),(26,true),(987,false)]
theorem inputList14602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14602
  have he : decodeClause inputClause14602 = containClause5 27 26 := by decide
  rw [he]
  exact input_contain 27 26 (by decide) v hb
mask_input "14602|1307993905256673975767120421215822522657964858038981454399109360803651185455244290152830052265253733065911465963809993683089776960073625541502023629723947119620918917825223508962533521125777727280023703876104306028269279939868013618062200188730110219063866757530095479450736063434158250346338582528|201326592"
def inputClause14603 : CNF.NClause := [(27,true),(28,true),(989,false)]
theorem inputList14603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14603 = (containClause5 27 28) := by decide
  rw [he]
  exact input_contain 27 28 (by decide) v hb
mask_input "14603|5231975621026695903068481684863290090631859432155925817596437443214604741820977160611320209061014932263645863855239974732359107840294502166008094518895788478483675671300894035850134084503110909120094815504417224113077119759472054472248800754920440876255467030120381917802944253736633001385354330112|402653184"
def inputClause14604 : CNF.NClause := [(27,true),(29,true),(990,false)]
theorem inputList14604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14604 = (containClause5 27 29) := by decide
  rw [he]
  exact input_contain 27 29 (by decide) v hb
mask_input "14604|10463951242053391806136963369726580181263718864311851635192874886429209483641954321222640418122029864527291727710479949464718215680589004332016189037791576956967351342601788071700268169006221818240189631008834448226154239518944108944497601509840881752510934060240763835605888507473266002770708660224|671088640"
def inputClause14609 : CNF.NClause := [(28,true),(3,true),(995,false)]
theorem inputList14609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14609 = (containClause5 28 3) := by decide
  rw [he]
  exact input_contain 28 3 (by decide) v hb
mask_input "14609|334846439745708537796382827831250565800439003657979252326171996365734703476542538279124493379904955664873335286735358382870982901778848138624518049209330462622955242963257218294408581408199098183686068192282702343236935664606211486223923248314908216080349889927704442739388432239144512088662677127168|268435464"
def inputClause14612 : CNF.NClause := [(28,true),(6,true),(998,false)]
theorem inputList14612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14612 = (containClause5 28 6) := by decide
  rw [he]
  exact input_contain 28 6 (by decide) v hb
mask_input "14612|2678771517965668302371062622650004526403512029263834018609375970925877627812340306232995947039239645318986682293882867062967863214230785108996144393674643700983641943706057746355268651265592785469488545538261618745895485316849691889791385986519265728642799119421635541915107457913156096709301417017344|268435520"
def inputClause14619 : CNF.NClause := [(28,true),(13,true),(1005,false)]
theorem inputList14619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14619 = (containClause5 28 13) := by decide
  rw [he]
  exact input_contain 28 13 (by decide) v hb
mask_input "14619|342882754299605542703496015699200579379649539745770754382000124278512336359979559197823481221022674600830295333617006984059886491421540493951506482390354393725906168794375391533474387361995876540094533828897487199474622120556760561893297406274466013266278287285969349365133754612883980378790581378220032|268443648"
def inputClause14620 : CNF.NClause := [(28,true),(14,true),(1006,false)]
theorem inputList14620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14620 = (containClause5 28 14) := by decide
  rw [he]
  exact input_contain 28 14 (by decide) v hb
mask_input "14620|685765508599211085406992031398401158759299079491541508764000248557024672719959118395646962442045349201660590667234013968119772982843080987903012964780708787451812337588750783066948774723991753080189067657794974398949244241113521123786594812548932026532556574571938698730267509225767960757581162756440064|268451840"
def inputClause14621 : CNF.NClause := [(28,true),(15,true),(1007,false)]
theorem inputList14621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14621
  have he : decodeClause inputClause14621 = containClause5 28 15 := by decide
  rw [he]
  exact input_contain 28 15 (by decide) v hb
mask_input "14621|1371531017198422170813984062796802317518598158983083017528000497114049345439918236791293924884090698403321181334468027936239545965686161975806025929561417574903624675177501566133897549447983506160378135315589948797898488482227042247573189625097864053065113149143877397460535018451535921515162325512880128|268468224"
def inputClause14623 : CNF.NClause := [(28,true),(17,true),(1009,false)]
theorem inputList14623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14623 = (containClause5 28 17) := by decide
  rw [he]
  exact input_contain 28 17 (by decide) v hb
mask_input "14623|5486124068793688683255936251187209270074392635932332070112001988456197381759672947165175699536362793613284725337872111744958183862744647903224103718245670299614498700710006264535590197791934024641512541262359795191593953928908168990292758500391456212260452596575509589842140073806143686060649302051520512|268566528"
def inputClause14625 : CNF.NClause := [(28,true),(19,true),(1011,false)]
theorem inputList14625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14625 = (containClause5 28 19) := by decide
  rw [he]
  exact input_contain 28 19 (by decide) v hb
mask_input "14625|21944496275174754733023745004748837080297570543729328280448007953824789527038691788660702798145451174453138901351488446979832735450978591612896414872982681198457994802840025058142360791167736098566050165049439180766375815715632675961171034001565824849041810386302038359368560295224574744242597208206082048|268959744"
def inputClause14627 : CNF.NClause := [(28,true),(21,true),(1013,false)]
theorem inputList14627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14627 = (containClause5 28 21) := by decide
  rw [he]
  exact input_contain 28 21 (by decide) v hb
mask_input "14627|87777985100699018932094980018995348321190282174917313121792031815299158108154767154642811192581804697812555605405953787919330941803914366451585659491930724793831979211360100232569443164670944394264200660197756723065503262862530703844684136006263299396167241545208153437474241180898298976970388832824328192|270532608"
def inputClause14628 : CNF.NClause := [(28,true),(22,true),(1014,false)]
theorem inputList14628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14628 = (containClause5 28 22) := by decide
  rw [he]
  exact input_contain 28 22 (by decide) v hb
mask_input "14628|175555970201398037864189960037990696642380564349834626243584063630598316216309534309285622385163609395625111210811907575838661883607828732903171318983861449587663958422720200465138886329341888788528401320395513446131006525725061407689368272012526598792334483090416306874948482361796597953940777665648656384|272629760"
def inputClause14629 : CNF.NClause := [(28,true),(23,true),(1015,false)]
theorem inputList14629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14629 = (containClause5 28 23) := by decide
  rw [he]
  exact input_contain 28 23 (by decide) v hb
mask_input "14629|351111940402796075728379920075981393284761128699669252487168127261196632432619068618571244770327218791250222421623815151677323767215657465806342637967722899175327916845440400930277772658683777577056802640791026892262013051450122815378736544025053197584668966180832613749896964723593195907881555331297312768|276824064"
def inputClause14630 : CNF.NClause := [(28,true),(24,true),(1016,false)]
theorem inputList14630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14630 = (containClause5 28 24) := by decide
  rw [he]
  exact input_contain 28 24 (by decide) v hb
mask_input "14630|702223880805592151456759840151962786569522257399338504974336254522393264865238137237142489540654437582500444843247630303354647534431314931612685275935445798350655833690880801860555545317367555154113605281582053784524026102900245630757473088050106395169337932361665227499793929447186391815763110662594625536|285212672"
def inputClause14633 : CNF.NClause := [(28,true),(27,true),(1019,false)]
theorem inputList14633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14633 = (containClause5 28 27) := by decide
  rw [he]
  exact input_contain 28 27 (by decide) v hb
mask_input "14633|5617791046444737211654078721215702292556178059194708039794690036179146118921905097897139916325235500660003558745981042426837180275450519452901482207483566386805246669527046414884444362538940441232908842252656430276192208823201965046059784704400851161354703458893321819998351435577491134526104885300757004288|402653184"
def inputClause14634 : CNF.NClause := [(28,true),(29,true),(1021,false)]
theorem inputList14634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14634 = (containClause5 28 29) := by decide
  rw [he]
  exact input_contain 28 29 (by decide) v hb
mask_input "14634|22471164185778948846616314884862809170224712236778832159178760144716584475687620391588559665300942002640014234983924169707348721101802077811605928829934265547220986678108185659537777450155761764931635369010625721104768835292807860184239138817603404645418813835573287279993405742309964538104419541203028017152|805306368"
def inputClause14639 : CNF.NClause := [(29,true),(3,true),(1026,false)]
theorem inputList14639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14639 = (containClause5 29 3) := by decide
  rw [he]
  exact input_contain 29 3 (by decide) v hb
mask_input "14639|719077253944926363091722076315609893447190791576922629093720324630930703222003852530833909289630144084480455519485573430635159075257666489971389722557896497511071573699461941105208878404984376477812331808340023075352602729369851525895652442163308948653402042738345192959788983753918865219341425318496896548864|536870920"
def inputClause14642 : CNF.NClause := [(29,true),(6,true),(1029,false)]
theorem inputList14642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14642 = (containClause5 29 6) := by decide
  rw [he]
  exact input_contain 29 6 (by decide) v hb
mask_input "14642|5752618031559410904733776610524879147577526332615381032749762597047445625776030820246671274317041152675843644155884587445081272602061331919771117780463171980088572589595695528841671027239875011822498654466720184602820821834958812207165219537306471589227216341906761543678311870031350921754731402547975172390912|536870976"
def inputClause14643 : CNF.NClause := [(29,true),(7,true),(1030,false)]
theorem inputList14643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14643 = (containClause5 29 7) := by decide
  rw [he]
  exact input_contain 29 7 (by decide) v hb
mask_input "14643|11505236063118821809467553221049758295155052665230762065499525194094891251552061640493342548634082305351687288311769174890162545204122663839542235560926343960177145179191391057683342054479750023644997308933440369205641643669917624414330439074612943178454432683813523087356623740062701843509462805095950344781824|536871040"
def inputClause14645 : CNF.NClause := [(29,true),(9,true),(1032,false)]
theorem inputList14645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14645 = (containClause5 29 9) := by decide
  rw [he]
  exact input_contain 29 9 (by decide) v hb
mask_input "14645|46020944252475287237870212884199033180620210660923048261998100776379565006208246561973370194536329221406749153247076699560650180816490655358168942243705375840708580716765564230733368217919000094579989235733761476822566574679670497657321756298451772713817730735254092349426494960250807374037851220383801379127296|536871424"
def inputClause14649 : CNF.NClause := [(29,true),(13,true),(1036,false)]
theorem inputList14649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14649 = (containClause5 29 13) := by decide
  rw [he]
  exact input_contain 29 13 (by decide) v hb
mask_input "14649|736335108039604595805923406147184530889923370574768772191969612422073040099331944991573923112581267542507986451953227192970402893063850485730703075899286013451337291468249027691733891486704001513279827771740183629161065194874727962517148100775228363421083691764065477590823919364012917984605619526140822066036736|536879104"
def inputClause14650 : CNF.NClause := [(29,true),(14,true),(1037,false)]
theorem inputList14650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14650 = (containClause5 29 14) := by decide
  rw [he]
  exact input_contain 29 14 (by decide) v hb
mask_input "14650|1472670216079209191611846812294369061779846741149537544383939224844146080198663889983147846225162535085015972903906454385940805786127700971461406151798572026902674582936498055383467782973408003026559655543480367258322130389749455925034296201550456726842167383528130955181647838728025835969211239052281644132073472|536887296"
end Percolation.MaskChain
