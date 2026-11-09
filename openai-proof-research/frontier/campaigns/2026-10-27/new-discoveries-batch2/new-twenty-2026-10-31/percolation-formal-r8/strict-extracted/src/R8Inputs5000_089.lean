import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14296 : CNF.NClause := [(17,true),(21,true),(672,false)]
theorem inputList14296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14296
  have he : decodeClause inputClause14296 = containClause5 17 21 := by decide
  rw [he]
  exact input_contain 17 21 (by decide) v hb
mask_input "14296|19595533242629369747791401605606558418088927130487463844933662202465281465266200982457647235235528838735010358900495684567911298014908298340170885513171109743249504533143507682501017145381579984990109696|2228224"
def inputClause14297 : CNF.NClause := [(17,true),(22,true),(673,false)]
theorem inputList14297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14297
  have he : decodeClause inputClause14297 = containClause5 17 22 := by decide
  rw [he]
  exact input_contain 17 22 (by decide) v hb
mask_input "14297|39191066485258739495582803211213116836177854260974927689867324404930562930532401964915294470471057677470020717800991369135822596029816596680341771026342219486499009066287015365002034290763159969980219392|4325376"
def inputClause14298 : CNF.NClause := [(17,true),(23,true),(674,false)]
theorem inputList14298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14298
  have he : decodeClause inputClause14298 = containClause5 17 23 := by decide
  rw [he]
  exact input_contain 17 23 (by decide) v hb
mask_input "14298|78382132970517478991165606422426233672355708521949855379734648809861125861064803929830588940942115354940041435601982738271645192059633193360683542052684438972998018132574030730004068581526319939960438784|8519680"
def inputClause14299 : CNF.NClause := [(17,true),(24,true),(675,false)]
theorem inputList14299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14299 = (containClause5 17 24) := by decide
  rw [he]
  exact input_contain 17 24 (by decide) v hb
mask_input "14299|156764265941034957982331212844852467344711417043899710759469297619722251722129607859661177881884230709880082871203965476543290384119266386721367084105368877945996036265148061460008137163052639879920877568|16908288"
def inputClause14301 : CNF.NClause := [(17,true),(26,true),(677,false)]
theorem inputList14301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14301 = (containClause5 17 26) := by decide
  rw [he]
  exact input_contain 17 26 (by decide) v hb
mask_input "14301|627057063764139831929324851379409869378845668175598843037877190478889006888518431438644711527536922839520331484815861906173161536477065546885468336421475511783984145060592245840032548652210559519683510272|67239936"
def inputClause14302 : CNF.NClause := [(17,true),(27,true),(678,false)]
theorem inputList14302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14302 = (containClause5 17 27) := by decide
  rw [he]
  exact input_contain 17 27 (by decide) v hb
mask_input "14302|1254114127528279663858649702758819738757691336351197686075754380957778013777036862877289423055073845679040662969631723812346323072954131093770936672842951023567968290121184491680065097304421119039367020544|134348800"
def inputClause14303 : CNF.NClause := [(17,true),(28,true),(679,false)]
theorem inputList14303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14303 = (containClause5 17 28) := by decide
  rw [he]
  exact input_contain 17 28 (by decide) v hb
mask_input "14303|2508228255056559327717299405517639477515382672702395372151508761915556027554073725754578846110147691358081325939263447624692646145908262187541873345685902047135936580242368983360130194608842238078734041088|268566528"
def inputClause14304 : CNF.NClause := [(17,true),(29,true),(680,false)]
theorem inputList14304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14304
  have he : decodeClause inputClause14304 = containClause5 17 29 := by decide
  rw [he]
  exact input_contain 17 29 (by decide) v hb
mask_input "14304|5016456510113118655434598811035278955030765345404790744303017523831112055108147451509157692220295382716162651878526895249385292291816524375083746691371804094271873160484737966720260389217684476157468082176|537001984"
def inputClause14309 : CNF.NClause := [(18,true),(3,true),(685,false)]
theorem inputList14309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14309 = (containClause5 18 3) := by decide
  rw [he]
  exact input_contain 18 3 (by decide) v hb
mask_input "14309|160526608323619796973907161953128926560984491052953303817696560762595585763460718448293046151049452246917204860112860647980329353338128780002679894123897731016699941135511614935048332454965903237038978629632|262152"
def inputClause14312 : CNF.NClause := [(18,true),(6,true),(688,false)]
theorem inputList14312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14312
  have he : decodeClause inputClause14312 = containClause5 18 6 := by decide
  rw [he]
  exact input_contain 18 6 (by decide) v hb
mask_input "14312|1284212866588958375791257295625031412487875928423626430541572486100764686107685747586344369208395617975337638880902885183842634826705030240021439152991181848133599529084092919480386659639727225896311829037056|262208"
def inputClause14313 : CNF.NClause := [(18,true),(7,true),(689,false)]
theorem inputList14313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14313 = (containClause5 18 7) := by decide
  rw [he]
  exact input_contain 18 7 (by decide) v hb
mask_input "14313|2568425733177916751582514591250062824975751856847252861083144972201529372215371495172688738416791235950675277761805770367685269653410060480042878305982363696267199058168185838960773319279454451792623658074112|262272"
def inputClause14315 : CNF.NClause := [(18,true),(9,true),(691,false)]
theorem inputList14315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14315 = (containClause5 18 9) := by decide
  rw [he]
  exact input_contain 18 9 (by decide) v hb
mask_input "14315|10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170494632296448|262656"
def inputClause14318 : CNF.NClause := [(18,true),(12,true),(694,false)]
theorem inputList14318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14318 = (containClause5 18 12) := by decide
  rw [he]
  exact input_contain 18 12 (by decide) v hb
mask_input "14318|82189623461693336050640466920002010399224059419112091554660639110448939910891887845526039629337319550421608888377784651765928628909121935361372105791435638280550369861381946846744746216942542457363957058371584|266240"
def inputClause14319 : CNF.NClause := [(18,true),(13,true),(695,false)]
theorem inputList14319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14319 = (containClause5 18 13) := by decide
  rw [he]
  exact input_contain 18 13 (by decide) v hb
mask_input "14319|164379246923386672101280933840004020798448118838224183109321278220897879821783775691052079258674639100843217776755569303531857257818243870722744211582871276561100739722763893693489492433885084914727914116743168|270336"
def inputClause14320 : CNF.NClause := [(18,true),(14,true),(696,false)]
theorem inputList14320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14320 = (containClause5 18 14) := by decide
  rw [he]
  exact input_contain 18 14 (by decide) v hb
mask_input "14320|328758493846773344202561867680008041596896237676448366218642556441795759643567551382104158517349278201686435553511138607063714515636487741445488423165742553122201479445527787386978984867770169829455828233486336|278528"
def inputClause14321 : CNF.NClause := [(18,true),(15,true),(697,false)]
theorem inputList14321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14321 = (containClause5 18 15) := by decide
  rw [he]
  exact input_contain 18 15 (by decide) v hb
mask_input "14321|657516987693546688405123735360016083193792475352896732437285112883591519287135102764208317034698556403372871107022277214127429031272975482890976846331485106244402958891055574773957969735540339658911656466972672|294912"
def inputClause14322 : CNF.NClause := [(18,true),(16,true),(698,false)]
theorem inputList14322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14322 = (containClause5 18 16) := by decide
  rw [he]
  exact input_contain 18 16 (by decide) v hb
mask_input "14322|1315033975387093376810247470720032166387584950705793464874570225767183038574270205528416634069397112806745742214044554428254858062545950965781953692662970212488805917782111149547915939471080679317823312933945344|327680"
def inputClause14323 : CNF.NClause := [(18,true),(17,true),(699,false)]
theorem inputList14323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14323 = (containClause5 18 17) := by decide
  rw [he]
  exact input_contain 18 17 (by decide) v hb
mask_input "14323|2630067950774186753620494941440064332775169901411586929749140451534366077148540411056833268138794225613491484428089108856509716125091901931563907385325940424977611835564222299095831878942161358635646625867890688|393216"
def inputClause14324 : CNF.NClause := [(18,true),(19,true),(701,false)]
theorem inputList14324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14324 = (containClause5 18 19) := by decide
  rw [he]
  exact input_contain 18 19 (by decide) v hb
mask_input "14324|10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586503471562752|786432"
def inputClause14325 : CNF.NClause := [(18,true),(20,true),(702,false)]
theorem inputList14325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14325 = (containClause5 18 20) := by decide
  rw [he]
  exact input_contain 18 20 (by decide) v hb
mask_input "14325|21040543606193494028963959531520514662201359211292695437993123612274928617188323288454666145110353804907931875424712870852077729000735215452511259082607523399820894684513778392766655031537290869085173006943125504|1310720"
def inputClause14326 : CNF.NClause := [(18,true),(21,true),(703,false)]
theorem inputList14326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14326 = (containClause5 18 21) := by decide
  rw [he]
  exact input_contain 18 21 (by decide) v hb
mask_input "14326|42081087212386988057927919063041029324402718422585390875986247224549857234376646576909332290220707609815863750849425741704155458001470430905022518165215046799641789369027556785533310063074581738170346013886251008|2359296"
def inputClause14327 : CNF.NClause := [(18,true),(22,true),(704,false)]
theorem inputList14327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14327 = (containClause5 18 22) := by decide
  rw [he]
  exact input_contain 18 22 (by decide) v hb
mask_input "14327|84162174424773976115855838126082058648805436845170781751972494449099714468753293153818664580441415219631727501698851483408310916002940861810045036330430093599283578738055113571066620126149163476340692027772502016|4456448"
def inputClause14328 : CNF.NClause := [(18,true),(23,true),(705,false)]
theorem inputList14328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14328
  have he : decodeClause inputClause14328 = containClause5 18 23 := by decide
  rw [he]
  exact input_contain 18 23 (by decide) v hb
mask_input "14328|168324348849547952231711676252164117297610873690341563503944988898199428937506586307637329160882830439263455003397702966816621832005881723620090072660860187198567157476110227142133240252298326952681384055545004032|8650752"
def inputClause14329 : CNF.NClause := [(18,true),(24,true),(706,false)]
theorem inputList14329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14329 = (containClause5 18 24) := by decide
  rw [he]
  exact input_contain 18 24 (by decide) v hb
mask_input "14329|336648697699095904463423352504328234595221747380683127007889977796398857875013172615274658321765660878526910006795405933633243664011763447240180145321720374397134314952220454284266480504596653905362768111090008064|17039360"
def inputClause14331 : CNF.NClause := [(18,true),(26,true),(708,false)]
theorem inputList14331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14331 = (containClause5 18 26) := by decide
  rw [he]
  exact input_contain 18 26 (by decide) v hb
mask_input "14331|1346594790796383617853693410017312938380886989522732508031559911185595431500052690461098633287062643514107640027181623734532974656047053788960720581286881497588537259808881817137065922018386615621451072444360032256|67371008"
def inputClause14332 : CNF.NClause := [(18,true),(27,true),(709,false)]
theorem inputList14332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14332 = (containClause5 18 27) := by decide
  rw [he]
  exact input_contain 18 27 (by decide) v hb
mask_input "14332|2693189581592767235707386820034625876761773979045465016063119822371190863000105380922197266574125287028215280054363247469065949312094107577921441162573762995177074519617763634274131844036773231242902144888720064512|134479872"
def inputClause14333 : CNF.NClause := [(18,true),(28,true),(710,false)]
theorem inputList14333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14333 = (containClause5 18 28) := by decide
  rw [he]
  exact input_contain 18 28 (by decide) v hb
mask_input "14333|5386379163185534471414773640069251753523547958090930032126239644742381726000210761844394533148250574056430560108726494938131898624188215155842882325147525990354149039235527268548263688073546462485804289777440129024|268697600"
def inputClause14334 : CNF.NClause := [(18,true),(29,true),(711,false)]
theorem inputList14334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14334 = (containClause5 18 29) := by decide
  rw [he]
  exact input_contain 18 29 (by decide) v hb
mask_input "14334|10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579554880258048|537133056"
def inputClause14339 : CNF.NClause := [(19,true),(3,true),(716,false)]
theorem inputList14339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14339 = (containClause5 19 3) := by decide
  rw [he]
  exact input_contain 19 3 (by decide) v hb
mask_input "14339|344728266443874206170545512964432112225507069317819522056079337263512430464013488758041250121488036739611555846958495676040441511948045769973944468809441663382665538511073745187088876036706973599091474545756168257536|524296"
def inputClause14342 : CNF.NClause := [(19,true),(6,true),(719,false)]
theorem inputList14342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14342 = (containClause5 19 6) := by decide
  rw [he]
  exact input_contain 19 6 (by decide) v hb
mask_input "14342|2757826131550993649364364103715456897804056554542556176448634698108099443712107910064330000971904293916892446775667965408323532095584366159791555750475533307061324308088589961496711008293655788792731796366049346060288|524352"
def inputClause14343 : CNF.NClause := [(19,true),(7,true),(720,false)]
theorem inputList14343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14343
  have he : decodeClause inputClause14343 = containClause5 19 7 := by decide
  rw [he]
  exact input_contain 19 7 (by decide) v hb
mask_input "14343|5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893551335930816647064191168732319583111500951066614122648616177179922993422016587311577585463592732098692120576|524416"
def inputClause14345 : CNF.NClause := [(19,true),(9,true),(722,false)]
theorem inputList14345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14345
  have he : decodeClause inputClause14345 = containClause5 19 9 := by decide
  rw [he]
  exact input_contain 19 9 (by decide) v hb
mask_input "14345|22062609052407949194914912829723655182432452436340449411589077584864795549696863280514640007775234351335139574205343723266588256764674929278332446003804266456490594464708719691973688066349246310341854370928394768482304|524800"
def inputClause14348 : CNF.NClause := [(19,true),(12,true),(725,false)]
theorem inputList14348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14348 = (containClause5 19 12) := by decide
  rw [he]
  exact input_contain 19 12 (by decide) v hb
mask_input "14348|176500872419263593559319302637789241459459619490723595292712620678918364397574906244117120062201874810681116593642749786132706054117399434226659568030434131651924755717669757535789504530793970482734834967427158147858432|528384"
def inputClause14349 : CNF.NClause := [(19,true),(13,true),(726,false)]
theorem inputList14349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14349 = (containClause5 19 13) := by decide
  rw [he]
  exact input_contain 19 13 (by decide) v hb
mask_input "14349|353001744838527187118638605275578482918919238981447190585425241357836728795149812488234240124403749621362233187285499572265412108234798868453319136060868263303849511435339515071579009061587940965469669934854316295716864|532480"
def inputClause14351 : CNF.NClause := [(19,true),(15,true),(728,false)]
theorem inputList14351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14351 = (containClause5 19 15) := by decide
  rw [he]
  exact input_contain 19 15 (by decide) v hb
mask_input "14351|1412006979354108748474554421102313931675676955925788762341700965431346915180599249952936960497614998485448932749141998289061648432939195473813276544243473053215398045741358060286316036246351763861878679739417265182867456|557056"
def inputClause14352 : CNF.NClause := [(19,true),(16,true),(729,false)]
theorem inputList14352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14352
  have he : decodeClause inputClause14352 = containClause5 19 16 := by decide
  rw [he]
  exact input_contain 19 16 (by decide) v hb
mask_input "14352|2824013958708217496949108842204627863351353911851577524683401930862693830361198499905873920995229996970897865498283996578123296865878390947626553088486946106430796091482716120572632072492703527723757359478834530365734912|589824"
def inputClause14353 : CNF.NClause := [(19,true),(17,true),(730,false)]
theorem inputList14353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14353 = (containClause5 19 17) := by decide
  rw [he]
  exact input_contain 19 17 (by decide) v hb
mask_input "14353|5648027917416434993898217684409255726702707823703155049366803861725387660722396999811747841990459993941795730996567993156246593731756781895253106176973892212861592182965432241145264144985407055447514718957669060731469824|655360"
def inputClause14354 : CNF.NClause := [(19,true),(18,true),(731,false)]
theorem inputList14354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14354 = (containClause5 19 18) := by decide
  rw [he]
  exact input_contain 19 18 (by decide) v hb
mask_input "14354|11296055834832869987796435368818511453405415647406310098733607723450775321444793999623495683980919987883591461993135986312493187463513563790506212353947784425723184365930864482290528289970814110895029437915338121462939648|786432"
def inputClause14355 : CNF.NClause := [(19,true),(20,true),(733,false)]
theorem inputList14355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14355 = (containClause5 19 20) := by decide
  rw [he]
  exact input_contain 19 20 (by decide) v hb
mask_input "14355|45184223339331479951185741475274045813621662589625240394934430893803101285779175998493982735923679951534365847972543945249972749854054255162024849415791137702892737463723457929162113159883256443580117751661352485851758592|1572864"
def inputClause14356 : CNF.NClause := [(19,true),(21,true),(734,false)]
theorem inputList14356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14356 = (containClause5 19 21) := by decide
  rw [he]
  exact input_contain 19 21 (by decide) v hb
mask_input "14356|90368446678662959902371482950548091627243325179250480789868861787606202571558351996987965471847359903068731695945087890499945499708108510324049698831582275405785474927446915858324226319766512887160235503322704971703517184|2621440"
end Percolation.MaskChain
