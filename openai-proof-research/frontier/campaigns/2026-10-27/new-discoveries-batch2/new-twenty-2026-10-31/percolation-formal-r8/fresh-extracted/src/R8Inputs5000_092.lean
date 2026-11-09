import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14479 : CNF.NClause := [(23,true),(24,true),(861,false)]
theorem inputList14479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14479 = (containClause5 23 24) := by decide
  rw [he]
  exact input_contain 23 24 (by decide) v hb
mask_input "14479|15375394465392026070980930960402958051966483647589383243116337952281869440244186537876296086692518667977838631290276787444086150484586994200087471936798525767761360737466168478385414860572969804431318564695864578364068534363514095860253929241066696020120829952|25165824"
def inputClause14481 : CNF.NClause := [(23,true),(26,true),(863,false)]
theorem inputList14481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14481 = (containClause5 23 26) := by decide
  rw [he]
  exact input_contain 23 26 (by decide) v hb
mask_input "14481|61501577861568104283923723841611832207865934590357532972465351809127477760976746151505184346770074671911354525161107149776344601938347976800349887747194103071045442949864673913541659442291879217725274258783458313456274137454056383441015716964266784080483319808|75497472"
def inputClause14482 : CNF.NClause := [(23,true),(27,true),(864,false)]
theorem inputList14482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14482 = (containClause5 23 27) := by decide
  rw [he]
  exact input_contain 23 27 (by decide) v hb
mask_input "14482|123003155723136208567847447683223664415731869180715065944930703618254955521953492303010368693540149343822709050322214299552689203876695953600699775494388206142090885899729347827083318884583758435450548517566916626912548274908112766882031433928533568160966639616|142606336"
def inputClause14483 : CNF.NClause := [(23,true),(28,true),(865,false)]
theorem inputList14483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14483 = (containClause5 23 28) := by decide
  rw [he]
  exact input_contain 23 28 (by decide) v hb
mask_input "14483|246006311446272417135694895366447328831463738361430131889861407236509911043906984606020737387080298687645418100644428599105378407753391907201399550988776412284181771799458695654166637769167516870901097035133833253825096549816225533764062867857067136321933279232|276824064"
def inputClause14484 : CNF.NClause := [(23,true),(29,true),(866,false)]
theorem inputList14484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14484 = (containClause5 23 29) := by decide
  rw [he]
  exact input_contain 23 29 (by decide) v hb
mask_input "14484|492012622892544834271389790732894657662927476722860263779722814473019822087813969212041474774160597375290836201288857198210756815506783814402799101977552824568363543598917391308333275538335033741802194070267666507650193099632451067528125735714134272643866558464|545259520"
def inputClause14489 : CNF.NClause := [(24,true),(3,true),(871,false)]
theorem inputList14489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14489 = (containClause5 24 3) := by decide
  rw [he]
  exact input_contain 24 3 (by decide) v hb
mask_input "14489|15744403932561434696684473303452629045213679255131528440951130063136634306810047014785327192773139116009306758441243430342744218096217082060889571263281690386187633395165356521866664817226721079737670210248565328244806179188238434160900023542852296724603729870848|16777224"
def inputClause14492 : CNF.NClause := [(24,true),(6,true),(874,false)]
theorem inputList14492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14492 = (containClause5 24 6) := by decide
  rw [he]
  exact input_contain 24 6 (by decide) v hb
mask_input "14492|125955231460491477573475786427621032361709434041052227527609040505093074454480376118282617542185112928074454067529947442741953744769736656487116570106253523089501067161322852174933318537813768637901361681988522625958449433505907473287200188342818373796829838966784|16777280"
def inputClause14493 : CNF.NClause := [(24,true),(7,true),(875,false)]
theorem inputList14493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14493 = (containClause5 24 7) := by decide
  rw [he]
  exact input_contain 24 7 (by decide) v hb
mask_input "14493|251910462920982955146951572855242064723418868082104455055218081010186148908960752236565235084370225856148908135059894885483907489539473312974233140212507046179002134322645704349866637075627537275802723363977045251916898867011814946574400376685636747593659677933568|16777344"
def inputClause14495 : CNF.NClause := [(24,true),(9,true),(877,false)]
theorem inputList14495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14495 = (containClause5 24 9) := by decide
  rw [he]
  exact input_contain 24 9 (by decide) v hb
mask_input "14495|1007641851683931820587806291420968258893675472328417820220872324040744595635843008946260940337480903424595632540239579541935629958157893251896932560850028184716008537290582817399466548302510149103210893455908181007667595468047259786297601506742546990374638711734272|16777728"
def inputClause14498 : CNF.NClause := [(24,true),(12,true),(880,false)]
theorem inputList14498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14498 = (containClause5 24 12) := by decide
  rw [he]
  exact input_contain 24 12 (by decide) v hb
mask_input "14498|8061134813471454564702450331367746071149403778627342561766978592325956765086744071570087522699847227396765060321916636335485039665263146015175460486800225477728068298324662539195732386420081192825687147647265448061340763744378078290380812053940375922997109693874176|16781312"
def inputClause14499 : CNF.NClause := [(24,true),(13,true),(881,false)]
theorem inputList14499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14499 = (containClause5 24 13) := by decide
  rw [he]
  exact input_contain 24 13 (by decide) v hb
mask_input "14499|16122269626942909129404900662735492142298807557254685123533957184651913530173488143140175045399694454793530120643833272670970079330526292030350920973600450955456136596649325078391464772840162385651374295294530896122681527488756156580761624107880751845994219387748352|16785408"
def inputClause14501 : CNF.NClause := [(24,true),(15,true),(883,false)]
theorem inputList14501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14501 = (containClause5 24 15) := by decide
  rw [he]
  exact input_contain 24 15 (by decide) v hb
mask_input "14501|64489078507771636517619602650941968569195230229018740494135828738607654120693952572560700181598777819174120482575333090683880317322105168121403683894401803821824546386597300313565859091360649542605497181178123584490726109955024626323046496431523007383976877550993408|16809984"
def inputClause14502 : CNF.NClause := [(24,true),(16,true),(884,false)]
theorem inputList14502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14502 = (containClause5 24 16) := by decide
  rw [he]
  exact input_contain 24 16 (by decide) v hb
mask_input "14502|128978157015543273035239205301883937138390460458037480988271657477215308241387905145121400363197555638348240965150666181367760634644210336242807367788803607643649092773194600627131718182721299085210994362356247168981452219910049252646092992863046014767953755101986816|16842752"
def inputClause14503 : CNF.NClause := [(24,true),(17,true),(885,false)]
theorem inputList14503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14503 = (containClause5 24 17) := by decide
  rw [he]
  exact input_contain 24 17 (by decide) v hb
mask_input "14503|257956314031086546070478410603767874276780920916074961976543314954430616482775810290242800726395111276696481930301332362735521269288420672485614735577607215287298185546389201254263436365442598170421988724712494337962904439820098505292185985726092029535907510203973632|16908288"
def inputClause14504 : CNF.NClause := [(24,true),(18,true),(886,false)]
theorem inputList14504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14504 = (containClause5 24 18) := by decide
  rw [he]
  exact input_contain 24 18 (by decide) v hb
mask_input "14504|515912628062173092140956821207535748553561841832149923953086629908861232965551620580485601452790222553392963860602664725471042538576841344971229471155214430574596371092778402508526872730885196340843977449424988675925808879640197010584371971452184059071815020407947264|17039360"
def inputClause14505 : CNF.NClause := [(24,true),(19,true),(887,false)]
theorem inputList14505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14505 = (containClause5 24 19) := by decide
  rw [he]
  exact input_contain 24 19 (by decide) v hb
mask_input "14505|1031825256124346184281913642415071497107123683664299847906173259817722465931103241160971202905580445106785927721205329450942085077153682689942458942310428861149192742185556805017053745461770392681687954898849977351851617759280394021168743942904368118143630040815894528|17301504"
def inputClause14506 : CNF.NClause := [(24,true),(20,true),(888,false)]
theorem inputList14506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14506 = (containClause5 24 20) := by decide
  rw [he]
  exact input_contain 24 20 (by decide) v hb
mask_input "14506|2063650512248692368563827284830142994214247367328599695812346519635444931862206482321942405811160890213571855442410658901884170154307365379884917884620857722298385484371113610034107490923540785363375909797699954703703235518560788042337487885808736236287260081631789056|17825792"
def inputClause14507 : CNF.NClause := [(24,true),(21,true),(889,false)]
theorem inputList14507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14507 = (containClause5 24 21) := by decide
  rw [he]
  exact input_contain 24 21 (by decide) v hb
mask_input "14507|4127301024497384737127654569660285988428494734657199391624693039270889863724412964643884811622321780427143710884821317803768340308614730759769835769241715444596770968742227220068214981847081570726751819595399909407406471037121576084674975771617472472574520163263578112|18874368"
def inputClause14508 : CNF.NClause := [(24,true),(22,true),(890,false)]
theorem inputList14508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14508 = (containClause5 24 22) := by decide
  rw [he]
  exact input_contain 24 22 (by decide) v hb
mask_input "14508|8254602048994769474255309139320571976856989469314398783249386078541779727448825929287769623244643560854287421769642635607536680617229461519539671538483430889193541937484454440136429963694163141453503639190799818814812942074243152169349951543234944945149040326527156224|20971520"
def inputClause14509 : CNF.NClause := [(24,true),(23,true),(891,false)]
theorem inputList14509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14509 = (containClause5 24 23) := by decide
  rw [he]
  exact input_contain 24 23 (by decide) v hb
mask_input "14509|16509204097989538948510618278641143953713978938628797566498772157083559454897651858575539246489287121708574843539285271215073361234458923039079343076966861778387083874968908880272859927388326282907007278381599637629625884148486304338699903086469889890298080653054312448|25165824"
def inputClause14511 : CNF.NClause := [(24,true),(26,true),(894,false)]
theorem inputList14511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14511 = (containClause5 24 26) := by decide
  rw [he]
  exact input_contain 24 26 (by decide) v hb
mask_input "14511|132073632783916311588084946229129151629711831509030380531990177256668475639181214868604313971914296973668598748314282169720586889875671384312634744615734894227096670999751271042182879419106610263256058227052797101037007073187890434709599224691759119122384645224434499584|83886080"
def inputClause14512 : CNF.NClause := [(24,true),(27,true),(895,false)]
theorem inputList14512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14512 = (containClause5 24 27) := by decide
  rw [he]
  exact input_contain 24 27 (by decide) v hb
mask_input "14512|264147265567832623176169892458258303259423663018060761063980354513336951278362429737208627943828593947337197496628564339441173779751342768625269489231469788454193341999502542084365758838213220526512116454105594202074014146375780869419198449383518238244769290448868999168|150994944"
def inputClause14513 : CNF.NClause := [(24,true),(28,true),(896,false)]
theorem inputList14513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14513 = (containClause5 24 28) := by decide
  rw [he]
  exact input_contain 24 28 (by decide) v hb
mask_input "14513|528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336|285212672"
def inputClause14514 : CNF.NClause := [(24,true),(29,true),(897,false)]
theorem inputList14514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14514 = (containClause5 24 29) := by decide
  rw [he]
  exact input_contain 24 29 (by decide) v hb
mask_input "14514|1056589062271330492704679569833033213037694652072243044255921418053347805113449718948834511775314375789348789986514257357764695119005371074501077956925879153816773367998010168337463035352852882106048465816422376808296056585503123477676793797534072952979077161795475996672|553648128"
def inputClause14549 : CNF.NClause := [(26,true),(3,true),(933,false)]
theorem inputList14549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14549 = (containClause5 26 3) := by decide
  rw [he]
  exact input_contain 26 3 (by decide) v hb
mask_input "14549|72608247484266751113186645417475613287659189534150120071082610318161164900410369802010171606257634306142515810068016262229227795192622349013224149467890362587059123068723626657357734855190319183117148231560128769827526792328021488679545846696711820459572514914753120743347917422592|67108872"
def inputClause14552 : CNF.NClause := [(26,true),(6,true),(936,false)]
theorem inputList14552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14552 = (containClause5 26 6) := by decide
  rw [he]
  exact input_contain 26 6 (by decide) v hb
mask_input "14552|580865979874134008905493163339804906301273516273200960568660882545289319203282958416081372850061074449140126480544130097833822361540978792105793195743122900696472984549789013258861878841522553464937185852481030158620214338624171909436366773573694563676580119318024965946783339380736|67108928"
def inputClause14553 : CNF.NClause := [(26,true),(7,true),(937,false)]
theorem inputList14553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14553 = (containClause5 26 7) := by decide
  rw [he]
  exact input_contain 26 7 (by decide) v hb
mask_input "14553|1161731959748268017810986326679609812602547032546401921137321765090578638406565916832162745700122148898280252961088260195667644723081957584211586391486245801392945969099578026517723757683045106929874371704962060317240428677248343818872733547147389127353160238636049931893566678761472|67108992"
def inputClause14558 : CNF.NClause := [(26,true),(12,true),(942,false)]
theorem inputList14558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14558 = (containClause5 26 12) := by decide
  rw [he]
  exact input_contain 26 12 (by decide) v hb
mask_input "14558|37175422711944576569951562453747514003281505041484861476394296482898516429010109338629207862403908764744968094754824326261364631138622642694770764527559865644574271011186496848567160245857443421755979894558785930151693717671947002203927473508716452075301127636353597820594133720367104|67112960"
def inputClause14559 : CNF.NClause := [(26,true),(13,true),(943,false)]
theorem inputList14559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14559 = (containClause5 26 13) := by decide
  rw [he]
  exact input_contain 26 13 (by decide) v hb
mask_input "14559|74350845423889153139903124907495028006563010082969722952788592965797032858020218677258415724807817529489936189509648652522729262277245285389541529055119731289148542022372993697134320491714886843511959789117571860303387435343894004407854947017432904150602255272707195641188267440734208|67117056"
def inputClause14561 : CNF.NClause := [(26,true),(15,true),(945,false)]
theorem inputList14561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14561 = (containClause5 26 15) := by decide
  rw [he]
  exact input_contain 26 15 (by decide) v hb
mask_input "14561|297403381695556612559612499629980112026252040331878891811154371863188131432080874709033662899231270117959744758038594610090917049108981141558166116220478925156594168089491974788537281966859547374047839156470287441213549741375576017631419788069731616602409021090828782564753069762936832|67141632"
def inputClause14562 : CNF.NClause := [(26,true),(16,true),(946,false)]
theorem inputList14562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14562 = (containClause5 26 16) := by decide
  rw [he]
  exact input_contain 26 16 (by decide) v hb
mask_input "14562|594806763391113225119224999259960224052504080663757783622308743726376262864161749418067325798462540235919489516077189220181834098217962283116332232440957850313188336178983949577074563933719094748095678312940574882427099482751152035262839576139463233204818042181657565129506139525873664|67174400"
def inputClause14563 : CNF.NClause := [(26,true),(17,true),(947,false)]
theorem inputList14563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14563 = (containClause5 26 17) := by decide
  rw [he]
  exact input_contain 26 17 (by decide) v hb
mask_input "14563|1189613526782226450238449998519920448105008161327515567244617487452752525728323498836134651596925080471838979032154378440363668196435924566232664464881915700626376672357967899154149127867438189496191356625881149764854198965502304070525679152278926466409636084363315130259012279051747328|67239936"
def inputClause14564 : CNF.NClause := [(26,true),(18,true),(948,false)]
theorem inputList14564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14564 = (containClause5 26 18) := by decide
  rw [he]
  exact input_contain 26 18 (by decide) v hb
mask_input "14564|2379227053564452900476899997039840896210016322655031134489234974905505051456646997672269303193850160943677958064308756880727336392871849132465328929763831401252753344715935798308298255734876378992382713251762299529708397931004608141051358304557852932819272168726630260518024558103494656|67371008"
def inputClause14565 : CNF.NClause := [(26,true),(19,true),(949,false)]
theorem inputList14565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14565 = (containClause5 26 19) := by decide
  rw [he]
  exact input_contain 26 19 (by decide) v hb
mask_input "14565|4758454107128905800953799994079681792420032645310062268978469949811010102913293995344538606387700321887355916128617513761454672785743698264930657859527662802505506689431871596616596511469752757984765426503524599059416795862009216282102716609115705865638544337453260521036049116206989312|67633152"
def inputClause14566 : CNF.NClause := [(26,true),(20,true),(950,false)]
theorem inputList14566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14566 = (containClause5 26 20) := by decide
  rw [he]
  exact input_contain 26 20 (by decide) v hb
mask_input "14566|9516908214257811601907599988159363584840065290620124537956939899622020205826587990689077212775400643774711832257235027522909345571487396529861315719055325605011013378863743193233193022939505515969530853007049198118833591724018432564205433218231411731277088674906521042072098232413978624|68157440"
def inputClause14567 : CNF.NClause := [(26,true),(21,true),(951,false)]
theorem inputList14567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14567 = (containClause5 26 21) := by decide
  rw [he]
  exact input_contain 26 21 (by decide) v hb
mask_input "14567|19033816428515623203815199976318727169680130581240249075913879799244040411653175981378154425550801287549423664514470055045818691142974793059722631438110651210022026757727486386466386045879011031939061706014098396237667183448036865128410866436462823462554177349813042084144196464827957248|69206016"
def inputClause14568 : CNF.NClause := [(26,true),(22,true),(952,false)]
theorem inputList14568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14568 = (containClause5 26 22) := by decide
  rw [he]
  exact input_contain 26 22 (by decide) v hb
mask_input "14568|38067632857031246407630399952637454339360261162480498151827759598488080823306351962756308851101602575098847329028940110091637382285949586119445262876221302420044053515454972772932772091758022063878123412028196792475334366896073730256821732872925646925108354699626084168288392929655914496|71303168"
def inputClause14569 : CNF.NClause := [(26,true),(23,true),(953,false)]
theorem inputList14569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14569 = (containClause5 26 23) := by decide
  rw [he]
  exact input_contain 26 23 (by decide) v hb
mask_input "14569|76135265714062492815260799905274908678720522324960996303655519196976161646612703925512617702203205150197694658057880220183274764571899172238890525752442604840088107030909945545865544183516044127756246824056393584950668733792147460513643465745851293850216709399252168336576785859311828992|75497472"
def inputClause14570 : CNF.NClause := [(26,true),(24,true),(954,false)]
theorem inputList14570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14570 = (containClause5 26 24) := by decide
  rw [he]
  exact input_contain 26 24 (by decide) v hb
mask_input "14570|152270531428124985630521599810549817357441044649921992607311038393952323293225407851025235404406410300395389316115760440366549529143798344477781051504885209680176214061819891091731088367032088255512493648112787169901337467584294921027286931491702587700433418798504336673153571718623657984|83886080"
def inputClause14572 : CNF.NClause := [(26,true),(27,true),(957,false)]
theorem inputList14572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14572 = (containClause5 26 27) := by decide
  rw [he]
  exact input_contain 26 27 (by decide) v hb
mask_input "14572|1218164251424999885044172798484398538859528357199375940858488307151618586345803262808201883235251282403163114528926083522932396233150386755822248412039081677441409712494559128733848706936256706044099949184902297359210699740674359368218295451933620701603467350388034693385228573748989263872|201326592"
end Percolation.MaskChain
