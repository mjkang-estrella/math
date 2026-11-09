import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9772 : CNF.NClause := [(407,true),(408,false),(414,true),(420,true),(426,true),(429,true)]
theorem inputList9772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) inputClause9772 (by decide) v hb
mask_input "9772|661055968790248598951915308032771039828404682964281219284648795274405791236311345825189210439715284847591212025023358304256|1562377026301110187808797422219554927094201932582369715546228545408463650935103086314291303143612948122390959403419618836022820864"
def inputClause9773 : CNF.NClause := [(407,false),(408,true),(414,true),(420,true),(426,true),(429,true)]
theorem inputList9773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 21) (closed_mem 9 21) inputClause9773 (by decide) v hb
mask_input "9773|330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128|1562377356829094582933096898177208943479721846784711197686838187732861288137998704469964215738218167980033383199025631347701972992"
def inputClause9775 : CNF.NClause := [(405,true),(408,true),(416,true),(419,true),(427,false),(431,true)]
theorem inputList9775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) inputClause9775 (by decide) v hb
mask_input "9775|346583711765101857447301773017885462929554634421977071896309947576827663475703202879996800763017447262173901370175446478621769728|5546863204881687340958487402060596448216058602096451189086562687283449530260774848270994101486994004890766725615426325626759413760"
def inputClause9776 : CNF.NClause := [(405,true),(408,true),(416,true),(419,false),(427,true),(431,true)]
theorem inputList9776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) inputClause9776 (by decide) v hb
mask_input "9776|1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288|5892093074022706769275135652527630796056044663727717413045777674127555210676026085514740914747030915249572760183374524267574067200"
def inputClause9779 : CNF.NClause := [(405,false),(408,true),(416,true),(419,true),(427,true),(431,true)]
theorem inputList9779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 22) (closed_mem 9 22) inputClause9779 (by decide) v hb
mask_input "9779|82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032|5893446834014793099624714306089068407049233257967842890447720224279177784435754146612072674101360147188530021036700268977461395456"
def inputClause9780 : CNF.NClause := [(406,true),(408,true),(415,true),(422,true),(424,true),(430,false)]
theorem inputList9780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 23) (closed_mem 9 23) inputClause9780 (by decide) v hb
mask_input "9780|2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824|54239146447263304857555437087607839239640732933707050831390970165668539366595918691447405824670809335281223253244147781345476608"
def inputClause9783 : CNF.NClause := [(406,true),(408,true),(415,false),(422,true),(424,true),(430,true)]
theorem inputList9783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 23) (closed_mem 9 23) inputClause9783 (by decide) v hb
mask_input "9783|84615164005151820665845159428194693098035799419427996068435045795123941278247852265624218936283556460491675139202989862944768|2826824225404073012615303776071263347982979772510104198005802115734494723230943293879156187709874103876211942539508516620456689664"
def inputClause9785 : CNF.NClause := [(406,false),(408,true),(415,true),(422,true),(424,true),(430,true)]
theorem inputList9785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 23) (closed_mem 9 23) inputClause9785 (by decide) v hb
mask_input "9785|165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064|2826908675304085966873819883251864534483317851208352884931565729618091028570773732653585355631507777503851222316844713354480058368"
def inputClause9786 : CNF.NClause := [(404,true),(408,true),(417,true),(421,true),(425,true),(432,false)]
theorem inputList9786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) inputClause9786 (by decide) v hb
mask_input "9786|11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296|92400461465592627806239300505603389682284910645991021255526559947620322931999843254866586341957735852347059817672441517653884928"
def inputClause9790 : CNF.NClause := [(404,true),(408,false),(417,true),(421,true),(425,true),(432,true)]
theorem inputList9790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 24) (closed_mem 9 24) inputClause9790 (by decide) v hb
mask_input "9790|661055968790248598951915308032771039828404682964281219284648795274405791236311345825189210439715284847591212025023358304256|11183078576892883275871297085162630170656993383744574357656225597757310279748711099103418385569305608526627056072074703810192211968"
def inputClause9808 : CNF.NClause := [(403,true),(410,false),(417,true),(419,true),(426,true),(430,true)]
theorem inputList9808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 27) (closed_mem 9 27) inputClause9808 (by decide) v hb
mask_input "9808|2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024|2947653873941467849410650691087943704787270103212840013673791357964212470694223157660014847901536799098790646636500730647523885056"
def inputClause9813 : CNF.NClause := [(403,true),(411,true),(414,false),(422,true),(425,true),(431,true)]
theorem inputList9813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 28) (closed_mem 9 28) inputClause9813 (by decide) v hb
mask_input "9813|42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384|5642821366281313963247942324517265331514225013557924258695338713820862443535303638515444070973724157200650263900090563948907069440"
def inputClause9820 : CNF.NClause := [(403,true),(409,false),(415,true),(421,true),(427,true),(429,true)]
theorem inputList9820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) inputClause9820 (by decide) v hb
mask_input "9820|1322111937580497197903830616065542079656809365928562438569297590548811582472622691650378420879430569695182424050046716608512|1738418565143843180275057517699613345723240493709794521859786118506096225886783100931979135083108493721904117222150802516180205568"
def inputClause9829 : CNF.NClause := [(459,true),(460,true),(461,true),(462,true),(463,false),(464,true)]
theorem inputList9829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 0) (closed_mem 10 0) inputClause9829 (by decide) v hb
mask_input "9829|23817051317718446589520242536874132581700120107002038199303870846751188192899823151552628349788604516295066307994130118526061826166445047808|69962588245797936856715712452067764458744102814318487210455120612331615316643230507685845777504025766616757279732757223170306614363932327936"
def inputClause9830 : CNF.NClause := [(459,true),(460,true),(461,true),(462,false),(463,true),(464,true)]
theorem inputList9830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 0) (closed_mem 10 0) inputClause9830 (by decide) v hb
mask_input "9830|11908525658859223294760121268437066290850060053501019099651935423375594096449911575776314174894302258147533153997065059263030913083222523904|81871113904657160151475833720504830749594162867819506310107056035707209413093142083462159952398328024764290433729822282433337527447154851840"
def inputClause9832 : CNF.NClause := [(459,true),(460,false),(461,true),(462,true),(463,true),(464,true)]
theorem inputList9832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 0) (closed_mem 10 0) inputClause9832 (by decide) v hb
mask_input "9832|2977131414714805823690030317109266572712515013375254774912983855843898524112477893944078543723575564536883288499266264815757728270805630976|90802508148801577622545924671832630467731707907945270634846007603238904985430575765294395583569054718374940299227621076880610712259571744768"
def inputClause9835 : CNF.NClause := [(438,true),(443,true),(448,true),(453,true),(458,false),(459,true)]
theorem inputList9835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 1) (closed_mem 10 1) inputClause9835 (by decide) v hb
mask_input "9835|744282853678701455922507579277316643178128753343813693728245963960974631028119473486019635930893891134220822124816566203939432067701407744|1512574808772733871877076562657965076761054302610721658344208144706407390884789420367067018239124747703102574223590118217060317162832396288"
def inputClause9837 : CNF.NClause := [(438,true),(443,true),(448,false),(453,true),(458,true),(459,true)]
theorem inputList9837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 1) (closed_mem 10 1) inputClause9837 (by decide) v hb
mask_input "9837|726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656|2256130823727139720909034818127393715404829414593848034012172618468201382624795495929760463119304875271762633826800418243066214628905189376"
def inputClause9838 : CNF.NClause := [(438,true),(443,false),(448,true),(453,true),(458,true),(459,true)]
theorem inputList9838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 1) (closed_mem 10 1) inputClause9838 (by decide) v hb
mask_input "9838|22713710134237715329666368996500141698551292521478689383796568724394977753543685103943470334805111423773828800195818060422956300894208|2256834948741301090084254475566285219797484504662013873383070312098657626935155350167982710699683833725899622519606488602939326274232909824"
def inputClause9842 : CNF.NClause := [(436,true),(441,true),(446,true),(451,false),(456,true),(459,true)]
theorem inputList9842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 2) (closed_mem 10 2) inputClause9842 (by decide) v hb
mask_input "9842|5814709794364855124394590463104036274829130885498544482251921593445114304907183386609528405710108524486100172850129423468276813028917248|1674823986336546160709262813936691358477159763118855834128230551514862337715499250305691589033135387886175982101476390987690808596156645376"
def inputClause9849 : CNF.NClause := [(437,true),(442,true),(447,false),(452,true),(457,true),(459,true)]
theorem inputList9849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 3) (closed_mem 10 3) inputClause9849 (by decide) v hb
mask_input "9849|363419362147803445274661903944002267176820680343659030140745099590319644056698961663095525356881782780381260803133088966767300814307328|1872348265542271316377024988341013500880543460640737710734332273195075322340517221450899867490546328770102139038216775325472539382154002432"
def inputClause9855 : CNF.NClause := [(435,true),(440,true),(445,false),(450,true),(455,true),(459,true)]
theorem inputList9855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 4) (closed_mem 10 4) inputClause9855 (by decide) v hb
mask_input "9855|90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832|1584511346903620012978017616001228339987328995175904968275952014240230777127308515591754420768977418893856767946779043137277282947090612224"
def inputClause9856 : CNF.NClause := [(435,true),(440,false),(445,true),(450,true),(455,true),(459,true)]
theorem inputList9856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 4) (closed_mem 10 4) inputClause9856 (by decide) v hb
mask_input "9856|2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776|1584599362530390184124920073181089778036410881434425698197314225944037807666103497371532201716524788700623891533379801932261421902756577280"
def inputClause9859 : CNF.NClause := [(454,true),(455,true),(456,true),(457,true),(458,false),(464,true)]
theorem inputList9859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 5) (closed_mem 10 5) inputClause9859 (by decide) v hb
mask_input "9859|744282853678701455922507579277316643178128753343813693728245963960974631028119473486019635930893891134220822124816566203939432067701407744|48331867810760675793967835929320749516379735920263901736477972284715790102388508309498400108262422055528464636730275767868316869896360165376"
def inputClause9863 : CNF.NClause := [(454,false),(455,true),(456,true),(457,true),(458,true),(464,true)]
theorem inputList9863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 5) (closed_mem 10 5) inputClause9863 (by decide) v hb
mask_input "9863|46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984|49029632986084458408895186784893233869359231626523727074348202875929203818977370315891543516947635078466796657472291298684510087459830235136"
def inputClause9864 : CNF.NClause := [(438,true),(442,true),(446,true),(450,true),(454,true),(463,false)]
theorem inputList9864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) inputClause9864 (by decide) v hb
mask_input "9864|23817051317718446589520242536874132581700120107002038199303870846751188192899823151552628349788604516295066307994130118526061826166445047808|49618809591683984066260235146885700169913378241061493167946848021213466245670978349724009179829728564965921946177770672308336256687800320"
def inputClause9867 : CNF.NClause := [(438,true),(442,true),(446,false),(450,true),(454,true),(463,true)]
theorem inputList9867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) inputClause9867 (by decide) v hb
mask_input "9867|181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664|23866488417629056671863865441069046280736445074902927862956747322222606499323465780421520811205755803968642039309906322653886778772725694464"
def inputClause9868 : CNF.NClause := [(438,true),(442,false),(446,true),(450,true),(454,true),(463,true)]
theorem inputList9868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 6) (closed_mem 10 6) inputClause9868 (by decide) v hb
mask_input "9868|11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104|23866658770455063454728837938836520031799184209596838953127125796488039461656617358059800387233266842304320343025907791289339950944982401024"
def inputClause9871 : CNF.NClause := [(436,true),(443,true),(445,true),(452,true),(454,false),(461,true)]
theorem inputList9871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) inputClause9871 (by decide) v hb
mask_input "9871|46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984|5966005995019872969937649160008231503840538064916086856289651348629002411059301572646935736168607362344790644721271269098582722003519668224"
def inputClause9872 : CNF.NClause := [(436,true),(443,true),(445,true),(452,false),(454,true),(461,true)]
theorem inputList9872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) inputClause9872 (by decide) v hb
mask_input "9872|11629419588729710248789180926208072549658261770997088964503843186890228609814366773219056811420217048972200345700258846936553626057834496|6000894253786062100684016702786855721489512850229078123183162878189673096888744672966592906602868013491707245758372045639392382881693171712"
def inputClause9874 : CNF.NClause := [(436,true),(443,false),(445,true),(452,true),(454,true),(461,true)]
theorem inputList9874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) inputClause9874 (by decide) v hb
mask_input "9874|22713710134237715329666368996500141698551292521478689383796568724394977753543685103943470334805111423773828800195818060422956300894208|6012500959664657573217476217344067293897472560707553733458282924807838930520805496054708019943953425429255672275272108668268513551450112000"
def inputClause9875 : CNF.NClause := [(436,false),(443,true),(445,true),(452,true),(454,true),(461,true)]
theorem inputList9875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 7) (closed_mem 10 7) inputClause9875 (by decide) v hb
mask_input "9875|177450860423732151013018507785157357019931972824052260810910693159335763699560039874558361990664932998233037501529828597054346100736|6012523495923931387200654870694556008881814092068102388095405910465870166162795340179772088855926239875746447871034802956500339453404905472"
def inputClause9877 : CNF.NClause := [(437,true),(440,true),(448,true),(451,true),(454,false),(462,true)]
theorem inputList9877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 8) (closed_mem 10 8) inputClause9877 (by decide) v hb
mask_input "9877|46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984|11915070401493371383953783417041198464491669184522715795135163431560696718086678749166967636401241962206373984886196482401347471476109869056"
def inputClause9887 : CNF.NClause := [(435,false),(441,true),(447,true),(453,true),(454,true),(460,true)]
theorem inputList9887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 9) (closed_mem 10 9) inputClause9887 (by decide) v hb
mask_input "9887|88725430211866075506509253892578678509965986412026130405455346579667881849780019937279180995332466499116518750764914298527173050368|3047277030036865448056872481162708135313066042504711337402493609207011314159859179466331965985037449891352815291470999940858923067042168832"
def inputClause9897 : CNF.NClause := [(438,true),(441,true),(444,false),(452,true),(455,true),(462,true)]
theorem inputList9897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 11) (closed_mem 10 11) inputClause9897 (by decide) v hb
mask_input "9897|45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416|12013196823388765941356660365439219209461837126991014566213859204842559890025734060896721170298115875525870893497717443959289389674202660864"
def inputClause9915 : CNF.NClause := [(435,true),(442,true),(444,false),(451,true),(458,true),(461,true)]
theorem inputList9915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 14) (closed_mem 10 14) inputClause9915 (by decide) v hb
mask_input "9915|45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416|6704371838483175289150703143652705967527515696592068939407287900981925570714741066383358160798103526620651885327118073932867675427665084416"
def inputClause9920 : CNF.NClause := [(449,true),(450,true),(451,true),(452,false),(453,true),(464,true)]
theorem inputList9920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 15) (closed_mem 10 15) inputClause9920 (by decide) v hb
mask_input "9920|11629419588729710248789180926208072549658261770997088964503843186890228609814366773219056811420217048972200345700258846936553626057834496|47667537216754491096005753968911113371980507716595693029380690242664685793052862607578261487910042156605927691982148481237066244007806369792"
def inputClause9923 : CNF.NClause := [(449,false),(450,true),(451,true),(452,true),(453,true),(464,true)]
theorem inputList9923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 15) (closed_mem 10 15) inputClause9923 (by decide) v hb
mask_input "9923|1453677448591213781098647615776009068707282721374636120562980398361278576226795846652382101427527131121525043212532355867069203257229312|47677712958894629592473444502221545435461458695645315482224631105453214743086450178504828162620034846523778367284636207728135728430606974976"
def inputClause9924 : CNF.NClause := [(438,true),(440,true),(447,true),(449,true),(456,true),(461,false)]
theorem inputList9924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 16) (closed_mem 10 16) inputClause9924 (by decide) v hb
mask_input "9924|5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456541611261952|187891359247622855850020464709204875277556690377128199627981434702058442692587354380617877776747694996117076495969837592390635607918903296"
def inputClause9926 : CNF.NClause := [(438,true),(440,true),(447,true),(449,false),(456,true),(461,true)]
theorem inputList9926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 10 16) (closed_mem 10 16) inputClause9926 (by decide) v hb
mask_input "9926|1453677448591213781098647615776009068707282721374636120562980398361278576226795846652382101427527131121525043212532355867069203257229312|6140700511228643289448982451311962011633879434406263113333386165991494212341316346422122583122471296938762128451289834868039022946272935936"
end Percolation.MaskChain
