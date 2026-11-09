import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14278 : CNF.NClause := [(17,true),(2,true),(653,false)]
theorem inputList14278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14278
  have he : decodeClause inputClause14278 = containClause5 17 2 := by decide
  rw [he]
  exact input_contain 17 2 (by decide) v hb
mask_input "14278|37375513539561023231108477793896786533525327931380202951304745106630862169773485150256437750311906506986637800026885384689161869077507588081685801531164378630160340372359290471078905382884178132992|131076"
def inputClause14280 : CNF.NClause := [(17,true),(4,true),(655,false)]
theorem inputList14280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14280 = (containClause5 17 4) := by decide
  rw [he]
  exact input_contain 17 4 (by decide) v hb
mask_input "14280|149502054158244092924433911175587146134101311725520811805218980426523448679093940601025751001247626027946551200107541538756647476310030352326743206124657514520641361489437161884315621531536712531968|131088"
def inputClause14281 : CNF.NClause := [(17,true),(5,true),(656,false)]
theorem inputList14281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14281 = (containClause5 17 5) := by decide
  rw [he]
  exact input_contain 17 5 (by decide) v hb
mask_input "14281|299004108316488185848867822351174292268202623451041623610437960853046897358187881202051502002495252055893102400215083077513294952620060704653486412249315029041282722978874323768631243063073425063936|131104"
def inputClause14284 : CNF.NClause := [(17,true),(8,true),(659,false)]
theorem inputList14284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14284 = (containClause5 17 8) := by decide
  rw [he]
  exact input_contain 17 8 (by decide) v hb
mask_input "14284|2392032866531905486790942578809394338145620987608332988883503686824375178865503049616412016019962016447144819201720664620106359620960485637227891297994520232330261783830994590149049944504587400511488|131328"
def inputClause14286 : CNF.NClause := [(17,true),(10,true),(661,false)]
theorem inputList14286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14286
  have he : decodeClause inputClause14286 = containClause5 17 10 := by decide
  rw [he]
  exact input_contain 17 10 (by decide) v hb
mask_input "14286|9568131466127621947163770315237577352582483950433331955534014747297500715462012198465648064079848065788579276806882658480425438483841942548911565191978080929321047135323978360596199778018349602045952|132096"
def inputClause14287 : CNF.NClause := [(17,true),(11,true),(662,false)]
theorem inputList14287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14287 = (containClause5 17 11) := by decide
  rw [he]
  exact input_contain 17 11 (by decide) v hb
mask_input "14287|19136262932255243894327540630475154705164967900866663911068029494595001430924024396931296128159696131577158553613765316960850876967683885097823130383956161858642094270647956721192399556036699204091904|133120"
def inputClause14310 : CNF.NClause := [(18,true),(4,true),(686,false)]
theorem inputList14310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14310 = (containClause5 18 4) := by decide
  rw [he]
  exact input_contain 18 4 (by decide) v hb
mask_input "14310|321053216647239593947814323906257853121968982105906607635393121525191171526921436896586092302098904493834409720225721295960658706676257560005359788247795462033399882271023229870096664909931806474077957259264|262160"
def inputClause14340 : CNF.NClause := [(19,true),(4,true),(717,false)]
theorem inputList14340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14340
  have he : decodeClause inputClause14340 = containClause5 19 4 := by decide
  rw [he]
  exact input_contain 19 4 (by decide) v hb
mask_input "14340|689456532887748412341091025928864224451014138635639044112158674527024860928026977516082500242976073479223111693916991352080883023896091539947888937618883326765331077022147490374177752073413947198182949091512336515072|524304"
def inputClause14367 : CNF.NClause := [(20,true),(1,true),(745,false)]
theorem inputList14367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14367 = (containClause5 20 1) := by decide
  rw [he]
  exact input_contain 20 1 (by decide) v hb
mask_input "14367|185074578797901741880056797082722491652594329967104984657651428941017502866551504889831353286343393081484762513295539999743888383402206229143653783207080500031048652651411283677848015502881818392904162310804899782048803192832|1048578"
def inputClause14368 : CNF.NClause := [(20,true),(2,true),(746,false)]
theorem inputList14368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14368 = (containClause5 20 2) := by decide
  rw [he]
  exact input_contain 20 2 (by decide) v hb
mask_input "14368|370149157595803483760113594165444983305188659934209969315302857882035005733103009779662706572686786162969525026591079999487776766804412458287307566414161000062097305302822567355696031005763636785808324621609799564097606385664|1048580"
def inputClause14370 : CNF.NClause := [(20,true),(4,true),(748,false)]
theorem inputList14370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14370 = (containClause5 20 4) := by decide
  rw [he]
  exact input_contain 20 4 (by decide) v hb
mask_input "14370|1480596630383213935040454376661779933220754639736839877261211431528140022932412039118650826290747144651878100106364319997951107067217649833149230265656644000248389221211290269422784124023054547143233298486439198256390425542656|1048592"
def inputClause14371 : CNF.NClause := [(20,true),(5,true),(749,false)]
theorem inputList14371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14371 = (containClause5 20 5) := by decide
  rw [he]
  exact input_contain 20 5 (by decide) v hb
mask_input "14371|2961193260766427870080908753323559866441509279473679754522422863056280045864824078237301652581494289303756200212728639995902214134435299666298460531313288000496778442422580538845568248046109094286466596972878396512780851085312|1048608"
def inputClause14374 : CNF.NClause := [(20,true),(8,true),(752,false)]
theorem inputList14374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14374 = (containClause5 20 8) := by decide
  rw [he]
  exact input_contain 20 8 (by decide) v hb
mask_input "14374|23689546086131422960647270026588478931532074235789438036179382904450240366918592625898413220651954314430049601701829119967217713075482397330387684250506304003974227539380644310764545984368872754291732775783027172102246808682496|1048832"
def inputClause14376 : CNF.NClause := [(20,true),(10,true),(754,false)]
theorem inputList14376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14376 = (containClause5 20 10) := by decide
  rw [he]
  exact input_contain 20 10 (by decide) v hb
mask_input "14376|94758184344525691842589080106353915726128296943157752144717531617800961467674370503593652882607817257720198406807316479868870852301929589321550737002025216015896910157522577243058183937475491017166931103132108688408987234729984|1049600"
def inputClause14377 : CNF.NClause := [(20,true),(11,true),(755,false)]
theorem inputList14377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14377 = (containClause5 20 11) := by decide
  rw [he]
  exact input_contain 20 11 (by decide) v hb
mask_input "14377|189516368689051383685178160212707831452256593886315504289435063235601922935348741007187305765215634515440396813614632959737741704603859178643101474004050432031793820315045154486116367874950982034333862206264217376817974469459968|1050624"
def inputClause14400 : CNF.NClause := [(21,true),(4,true),(779,false)]
theorem inputList14400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14400 = (containClause5 21 4) := by decide
  rw [he]
  exact input_contain 21 4 (by decide) v hb
mask_input "14400|3179557053031851899185109992371205233166102563054994659612778573877352351101699863205638981281067986842598872467724437926239395930347139873677900339284338973090723790890700606566943304973513615002138622348731328001828550356615286489088|2097168"
def inputClause14430 : CNF.NClause := [(22,true),(4,true),(810,false)]
theorem inputList14430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14430 = (containClause5 22 4) := by decide
  rw [he]
  exact input_contain 22 4 (by decide) v hb
mask_input "14430|6828046779268970776657768233698567984276232522051489956245767999246374131525255241237946573692471593720760228447675638216590132893818229842292076597586769967201441361422350907866192164773697561322460176523147880429251325990375896362151810433024|4194320"
def inputClause14457 : CNF.NClause := [(23,true),(1,true),(838,false)]
theorem inputList14457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14457 = (containClause5 23 1) := by decide
  rw [he]
  exact input_contain 23 1 (by decide) v hb
mask_input "14457|1832889850782397517082802171755189663406191307018921761884252780947908096342585866198098193012776216027479008590015982084761399088452696108828481666660133095712823955710669574545075280734654641679682560526831695838459555430831205351382962374814354898944|8388610"
def inputClause14458 : CNF.NClause := [(23,true),(2,true),(839,false)]
theorem inputList14458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14458 = (containClause5 23 2) := by decide
  rw [he]
  exact input_contain 23 2 (by decide) v hb
mask_input "14458|3665779701564795034165604343510379326812382614037843523768505561895816192685171732396196386025552432054958017180031964169522798176905392217656963333320266191425647911421339149090150561469309283359365121053663391676919110861662410702765924749628709797888|8388612"
def inputClause14460 : CNF.NClause := [(23,true),(4,true),(841,false)]
theorem inputList14460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14460 = (containClause5 23 4) := by decide
  rw [he]
  exact input_contain 23 4 (by decide) v hb
mask_input "14460|14663118806259180136662417374041517307249530456151374095074022247583264770740686929584785544102209728219832068720127856678091192707621568870627853333281064765702591645685356596360602245877237133437460484214653566707676443446649642811063698998514839191552|8388624"
def inputClause14461 : CNF.NClause := [(23,true),(5,true),(842,false)]
theorem inputList14461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14461 = (containClause5 23 5) := by decide
  rw [he]
  exact input_contain 23 5 (by decide) v hb
mask_input "14461|29326237612518360273324834748083034614499060912302748190148044495166529541481373859169571088204419456439664137440255713356182385415243137741255706666562129531405183291370713192721204491754474266874920968429307133415352886893299285622127397997029678383104|8388640"
def inputClause14464 : CNF.NClause := [(23,true),(8,true),(845,false)]
theorem inputList14464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14464 = (containClause5 23 8) := by decide
  rw [he]
  exact input_contain 23 8 (by decide) v hb
mask_input "14464|234609900900146882186598677984664276915992487298421985521184355961332236331850990873356568705635355651517313099522045706849459083321945101930045653332497036251241466330965705541769635934035794134999367747434457067322823095146394284977019183976237427064832|8388864"
def inputClause14466 : CNF.NClause := [(23,true),(10,true),(847,false)]
theorem inputList14466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14466 = (containClause5 23 10) := by decide
  rw [he]
  exact input_contain 23 10 (by decide) v hb
mask_input "14466|938439603600587528746394711938657107663969949193687942084737423845328945327403963493426274822541422606069252398088182827397836333287780407720182613329988145004965865323862822167078543736143176539997470989737828269291292380585577139908076735904949708259328|8389632"
def inputClause14467 : CNF.NClause := [(23,true),(11,true),(848,false)]
theorem inputList14467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14467 = (containClause5 23 11) := by decide
  rw [he]
  exact input_contain 23 11 (by decide) v hb
mask_input "14467|1876879207201175057492789423877314215327939898387375884169474847690657890654807926986852549645082845212138504796176365654795672666575560815440365226659976290009931730647725644334157087472286353079994941979475656538582584761171154279816153471809899416518656|8390656"
def inputClause14490 : CNF.NClause := [(24,true),(4,true),(872,false)]
theorem inputList14490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14490 = (containClause5 24 4) := by decide
  rw [he]
  exact input_contain 24 4 (by decide) v hb
mask_input "14490|31488807865122869393368946606905258090427358510263056881902260126273268613620094029570654385546278232018613516882486860685488436192434164121779142526563380772375266790330713043733329634453442159475340420497130656489612358376476868321800047085704593449207459741696|16777232"
def inputClause14550 : CNF.NClause := [(26,true),(4,true),(934,false)]
theorem inputList14550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14550 = (containClause5 26 4) := by decide
  rw [he]
  exact input_contain 26 4 (by decide) v hb
mask_input "14550|145216494968533502226373290834951226575318379068300240142165220636322329800820739604020343212515268612285031620136032524458455590385244698026448298935780725174118246137447253314715469710380638366234296463120257539655053584656042977359091693393423640919145029829506241486695834845184|67108880"
def inputClause14577 : CNF.NClause := [(27,true),(1,true),(962,false)]
theorem inputList14577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14577 = (containClause5 27 1) := by decide
  rw [he]
  exact input_contain 27 1 (by decide) v hb
mask_input "14577|38981256045599996321413529551500753243504907430380030107471625828851794763065704409862460263528041036901219664925634672733836679460812376186311949185250613678125110799825892119483158621960214593411198373916873515494742391701579499782985454461875862451310955212417110188327314359967656443904|134217730"
def inputClause14578 : CNF.NClause := [(27,true),(2,true),(963,false)]
theorem inputList14578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14578
  have he : decodeClause inputClause14578 = containClause5 27 2 := by decide
  rw [he]
  exact input_contain 27 2 (by decide) v hb
mask_input "14578|77962512091199992642827059103001506487009814860760060214943251657703589526131408819724920527056082073802439329851269345467673358921624752372623898370501227356250221599651784238966317243920429186822396747833747030989484783403158999565970908923751724902621910424834220376654628719935312887808|134217732"
def inputClause14580 : CNF.NClause := [(27,true),(4,true),(965,false)]
theorem inputList14580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14580 = (containClause5 27 4) := by decide
  rw [he]
  exact input_contain 27 4 (by decide) v hb
mask_input "14580|311850048364799970571308236412006025948039259443040240859773006630814358104525635278899682108224328295209757319405077381870693435686499009490495593482004909425000886398607136955865268975681716747289586991334988123957939133612635998263883635695006899610487641699336881506618514879741251551232|134217744"
def inputClause14581 : CNF.NClause := [(27,true),(5,true),(966,false)]
theorem inputList14581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14581 = (containClause5 27 5) := by decide
  rw [he]
  exact input_contain 27 5 (by decide) v hb
mask_input "14581|623700096729599941142616472824012051896078518886080481719546013261628716209051270557799364216448656590419514638810154763741386871372998018980991186964009818850001772797214273911730537951363433494579173982669976247915878267225271996527767271390013799220975283398673763013237029759482503102464|134217760"
def inputClause14584 : CNF.NClause := [(27,true),(8,true),(969,false)]
theorem inputList14584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14584
  have he : decodeClause inputClause14584 = containClause5 27 8 := by decide
  rw [he]
  exact input_contain 27 8 (by decide) v hb
mask_input "14584|4989600773836799529140931782592096415168628151088643853756368106093029729672410164462394913731589252723356117110481238109931094970983984151847929495712078550800014182377714191293844303610907467956633391861359809983327026137802175972222138171120110393767802267189390104105896238075860024819712|134217984"
def inputClause14586 : CNF.NClause := [(27,true),(10,true),(971,false)]
theorem inputList14586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14586 = (containClause5 27 10) := by decide
  rw [he]
  exact input_contain 27 10 (by decide) v hb
mask_input "14586|19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848|134218752"
def inputClause14587 : CNF.NClause := [(27,true),(11,true),(972,false)]
theorem inputList14587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14587 = (containClause5 27 11) := by decide
  rw [he]
  exact input_contain 27 11 (by decide) v hb
mask_input "14587|39916806190694396233127454260736771321349025208709150830050944848744237837379281315699159309852714021786848936883849904879448759767871873214783435965696628406400113459021713530350754428887259743653067134890878479866616209102417407777777105368960883150142418137515120832847169904606880198557696|134219776"
def inputClause14608 : CNF.NClause := [(28,true),(2,true),(994,false)]
theorem inputList14608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14608 = (containClause5 28 2) := by decide
  rw [he]
  exact input_contain 28 2 (by decide) v hb
mask_input "14608|167423219872854268898191413915625282900219501828989626163085998182867351738271269139562246689952477832436667643367679191435491450889424069312259024604665231311477621481628609147204290704099549091843034096141351171618467832303105743111961624157454108040174944963852221369694216119572256044331338563584|268435460"
def inputClause14610 : CNF.NClause := [(28,true),(4,true),(996,false)]
theorem inputList14610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14610 = (containClause5 28 4) := by decide
  rw [he]
  exact input_contain 28 4 (by decide) v hb
mask_input "14610|669692879491417075592765655662501131600878007315958504652343992731469406953085076558248986759809911329746670573470716765741965803557696277249036098418660925245910485926514436588817162816398196367372136384565404686473871329212422972447846496629816432160699779855408885478776864478289024177325354254336|268435472"
def inputClause14611 : CNF.NClause := [(28,true),(5,true),(997,false)]
theorem inputList14611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14611
  have he : decodeClause inputClause14611 = containClause5 28 5 := by decide
  rw [he]
  exact input_contain 28 5 (by decide) v hb
mask_input "14611|1339385758982834151185531311325002263201756014631917009304687985462938813906170153116497973519619822659493341146941433531483931607115392554498072196837321850491820971853028873177634325632796392734744272769130809372947742658424845944895692993259632864321399559710817770957553728956578048354650708508672|268435488"
def inputClause14614 : CNF.NClause := [(28,true),(8,true),(1000,false)]
theorem inputList14614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14614 = (containClause5 28 8) := by decide
  rw [he]
  exact input_contain 28 8 (by decide) v hb
mask_input "14614|10715086071862673209484250490600018105614048117055336074437503883703510511249361224931983788156958581275946729175531468251871452856923140435984577574698574803934567774824230985421074605062371141877954182153046474983581941267398767559165543946077062914571196477686542167660429831652624386837205668069376|268435712"
def inputClause14617 : CNF.NClause := [(28,true),(11,true),(1003,false)]
theorem inputList14617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14617 = (containClause5 28 11) := by decide
  rw [he]
  exact input_contain 28 11 (by decide) v hb
mask_input "14617|85720688574901385675874003924800144844912384936442688595500031069628084089994889799455870305255668650207573833404251746014971622855385123487876620597588598431476542198593847883368596840498969135023633457224371799868655530139190140473324351568616503316569571821492337341283438653220995094697645344555008|268437504"
def inputClause14640 : CNF.NClause := [(29,true),(4,true),(1027,false)]
theorem inputList14640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14640 = (containClause5 29 4) := by decide
  rw [he]
  exact input_contain 29 4 (by decide) v hb
mask_input "14640|1438154507889852726183444152631219786894381583153845258187440649261861406444007705061667818579260288168960911038971146861270318150515332979942779445115792995022143147398923882210417756809968752955624663616680046150705205458739703051791304884326617897306804085476690385919577967507837730438682850636993793097728|536870928"
end Percolation.MaskChain
