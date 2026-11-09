import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14395 : CNF.NClause := [(20,true),(30,true),(774,false)]
theorem inputList14395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14395 = (containClause5 20 30) := by decide
  rw [he]
  exact input_contain 20 30 (by decide) v hb
mask_input "14395|99361157907245371849534687261600163536440705095468583112899330433667260971928120725176218165033374588831214764616388685194981122823348121052434385602635592909085118465334393955216978280422300468816831948397854000057142198644227702784|1074790400"
def inputClause14396 : CNF.NClause := [(21,true),(0,true),(775,false)]
theorem inputList14396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14396
  have he : decodeClause inputClause14396 = containClause5 21 0 := by decide
  rw [he]
  exact input_contain 21 0 (by decide) v hb
mask_input "14396|198722315814490743699069374523200327072881410190937166225798660867334521943856241450352436330066749177662429529232777370389962245646696242104868771205271185818170236930668787910433956560844600937633663896795708000114284397288455405568|2097153"
def inputClause14420 : CNF.NClause := [(21,true),(25,true),(800,false)]
theorem inputList14420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14420
  have he : decodeClause inputClause14420 = containClause5 21 25 := by decide
  rw [he]
  exact input_contain 21 25 (by decide) v hb
mask_input "14420|6668014432879854274079851790721257797144758322315908160396257811764037237817632071521432200871554290742929910593433240445888801654119365080363356052330830046095157579514014558463078285911814024728965016135886601981690748037476461291163877376|35651584"
def inputClause14425 : CNF.NClause := [(21,true),(30,true),(805,false)]
theorem inputList14425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14425 = (containClause5 21 30) := by decide
  rw [he]
  exact input_contain 21 30 (by decide) v hb
mask_input "14425|213376461852155336770555257303080249508632266314109061132680249976449191610164226288685830427889737303773757138989863694268441652931819682571627393674586561475045042544448465870818505149178048791326880516348371263414103937199246761317244076032|1075838976"
def inputClause14426 : CNF.NClause := [(22,true),(0,true),(806,false)]
theorem inputList14426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14426 = (containClause5 22 0) := by decide
  rw [he]
  exact input_contain 22 0 (by decide) v hb
mask_input "14426|426752923704310673541110514606160499017264532628218122265360499952898383220328452577371660855779474607547514277979727388536883305863639365143254787349173122950090085088896931741637010298356097582653761032696742526828207874398493522634488152064|4194305"
def inputClause14450 : CNF.NClause := [(22,true),(25,true),(831,false)]
theorem inputList14450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14450 = (containClause5 22 25) := by decide
  rw [he]
  exact input_contain 22 25 (by decide) v hb
mask_input "14450|14319451959237480602209391966837419245360869586085326264720724851155532002676452079672642132912314187714679754609499860037198430378536688350222513020782289810256437153989606051133400630739489388122520004115872623737965276803368791807679393553237147648|37748736"
def inputClause14455 : CNF.NClause := [(22,true),(30,true),(836,false)]
theorem inputList14455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14455
  have he : decodeClause inputClause14455 = containClause5 22 30 := by decide
  rw [he]
  exact input_contain 22 30 (by decide) v hb
mask_input "14455|458222462695599379270700542938797415851547826754730440471063195236977024085646466549524548253194054006869752147503995521190349772113174027207120416665033273928205988927667393636268820183663660419920640131707923959614888857707801337845740593703588724736|1077936128"
def inputClause14456 : CNF.NClause := [(23,true),(0,true),(837,false)]
theorem inputList14456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14456 = (containClause5 23 0) := by decide
  rw [he]
  exact input_contain 23 0 (by decide) v hb
mask_input "14456|916444925391198758541401085877594831703095653509460880942126390473954048171292933099049096506388108013739504295007991042380699544226348054414240833330066547856411977855334787272537640367327320839841280263415847919229777715415602675691481187407177449472|8388609"
def inputClause14480 : CNF.NClause := [(23,true),(25,true),(862,false)]
theorem inputList14480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14480 = (containClause5 23 25) := by decide
  rw [he]
  exact input_contain 23 25 (by decide) v hb
mask_input "14480|30750788930784052141961861920805916103932967295178766486232675904563738880488373075752592173385037335955677262580553574888172300969173988400174943873597051535522721474932336956770829721145939608862637129391729156728137068727028191720507858482133392040241659904|41943040"
def inputClause14485 : CNF.NClause := [(23,true),(30,true),(867,false)]
theorem inputList14485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14485 = (containClause5 23 30) := by decide
  rw [he]
  exact input_contain 23 30 (by decide) v hb
mask_input "14485|984025245785089668542779581465789315325854953445720527559445628946039644175627938424082949548321194750581672402577714396421513631013567628805598203955105649136727087197834782616666551076670067483604388140535333015300386199264902135056251471428268545287733116928|1082130432"
def inputClause14486 : CNF.NClause := [(24,true),(0,true),(868,false)]
theorem inputList14486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14486 = (containClause5 24 0) := by decide
  rw [he]
  exact input_contain 24 0 (by decide) v hb
mask_input "14486|1968050491570179337085559162931578630651709906891441055118891257892079288351255876848165899096642389501163344805155428792843027262027135257611196407910211298273454174395669565233333102153340134967208776281070666030600772398529804270112502942856537090575466233856|16777217"
def inputClause14510 : CNF.NClause := [(24,true),(25,true),(893,false)]
theorem inputList14510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14510 = (containClause5 24 25) := by decide
  rw [he]
  exact input_contain 24 25 (by decide) v hb
mask_input "14510|66036816391958155794042473114564575814855915754515190265995088628334237819590607434302156985957148486834299374157141084860293444937835692156317372307867447113548335499875635521091439709553305131628029113526398550518503536593945217354799612345879559561192322612217249792|50331648"
def inputClause14515 : CNF.NClause := [(24,true),(30,true),(898,false)]
theorem inputList14515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14515 = (containClause5 24 30) := by decide
  rw [he]
  exact input_contain 24 30 (by decide) v hb
mask_input "14515|2113178124542660985409359139666066426075389304144486088511842836106695610226899437897669023550628751578697579973028514715529390238010742149002155913851758307633546735996020336674926070705705764212096931632844753616592113171006246955353587595068145905958154323590951993344|1090519040"
def inputClause14516 : CNF.NClause := [(25,true),(0,true),(899,false)]
theorem inputList14516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14516 = (containClause5 25 0) := by decide
  rw [he]
  exact input_contain 25 0 (by decide) v hb
mask_input "14516|4226356249085321970818718279332132852150778608288972177023685672213391220453798875795338047101257503157395159946057029431058780476021484298004311827703516615267093471992040673349852141411411528424193863265689507233184226342012493910707175190136291811916308647181903986688|33554433"
def inputClause14517 : CNF.NClause := [(25,true),(1,true),(900,false)]
theorem inputList14517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14517 = (containClause5 25 1) := by decide
  rw [he]
  exact input_contain 25 1 (by decide) v hb
mask_input "14517|8452712498170643941637436558664265704301557216577944354047371344426782440907597751590676094202515006314790319892114058862117560952042968596008623655407033230534186943984081346699704282822823056848387726531379014466368452684024987821414350380272583623832617294363807973376|33554434"
def inputClause14518 : CNF.NClause := [(25,true),(2,true),(901,false)]
theorem inputList14518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14518 = (containClause5 25 2) := by decide
  rw [he]
  exact input_contain 25 2 (by decide) v hb
mask_input "14518|16905424996341287883274873117328531408603114433155888708094742688853564881815195503181352188405030012629580639784228117724235121904085937192017247310814066461068373887968162693399408565645646113696775453062758028932736905368049975642828700760545167247665234588727615946752|33554436"
def inputClause14519 : CNF.NClause := [(25,true),(3,true),(902,false)]
theorem inputList14519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14519 = (containClause5 25 3) := by decide
  rw [he]
  exact input_contain 25 3 (by decide) v hb
mask_input "14519|33810849992682575766549746234657062817206228866311777416189485377707129763630391006362704376810060025259161279568456235448470243808171874384034494621628132922136747775936325386798817131291292227393550906125516057865473810736099951285657401521090334495330469177455231893504|33554440"
def inputClause14520 : CNF.NClause := [(25,true),(4,true),(903,false)]
theorem inputList14520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14520 = (containClause5 25 4) := by decide
  rw [he]
  exact input_contain 25 4 (by decide) v hb
mask_input "14520|67621699985365151533099492469314125634412457732623554832378970755414259527260782012725408753620120050518322559136912470896940487616343748768068989243256265844273495551872650773597634262582584454787101812251032115730947621472199902571314803042180668990660938354910463787008|33554448"
def inputClause14521 : CNF.NClause := [(25,true),(5,true),(904,false)]
theorem inputList14521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14521 = (containClause5 25 5) := by decide
  rw [he]
  exact input_contain 25 5 (by decide) v hb
mask_input "14521|135243399970730303066198984938628251268824915465247109664757941510828519054521564025450817507240240101036645118273824941793880975232687497536137978486512531688546991103745301547195268525165168909574203624502064231461895242944399805142629606084361337981321876709820927574016|33554464"
def inputClause14522 : CNF.NClause := [(25,true),(6,true),(905,false)]
theorem inputList14522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14522 = (containClause5 25 6) := by decide
  rw [he]
  exact input_contain 25 6 (by decide) v hb
mask_input "14522|270486799941460606132397969877256502537649830930494219329515883021657038109043128050901635014480480202073290236547649883587761950465374995072275956973025063377093982207490603094390537050330337819148407249004128462923790485888799610285259212168722675962643753419641855148032|33554496"
def inputClause14523 : CNF.NClause := [(25,true),(7,true),(906,false)]
theorem inputList14523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14523 = (containClause5 25 7) := by decide
  rw [he]
  exact input_contain 25 7 (by decide) v hb
mask_input "14523|540973599882921212264795939754513005075299661860988438659031766043314076218086256101803270028960960404146580473095299767175523900930749990144551913946050126754187964414981206188781074100660675638296814498008256925847580971777599220570518424337445351925287506839283710296064|33554560"
def inputClause14524 : CNF.NClause := [(25,true),(8,true),(907,false)]
theorem inputList14524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14524 = (containClause5 25 8) := by decide
  rw [he]
  exact input_contain 25 8 (by decide) v hb
mask_input "14524|1081947199765842424529591879509026010150599323721976877318063532086628152436172512203606540057921920808293160946190599534351047801861499980289103827892100253508375928829962412377562148201321351276593628996016513851695161943555198441141036848674890703850575013678567420592128|33554688"
def inputClause14525 : CNF.NClause := [(25,true),(9,true),(908,false)]
theorem inputList14525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14525 = (containClause5 25 9) := by decide
  rw [he]
  exact input_contain 25 9 (by decide) v hb
mask_input "14525|2163894399531684849059183759018052020301198647443953754636127064173256304872345024407213080115843841616586321892381199068702095603722999960578207655784200507016751857659924824755124296402642702553187257992033027703390323887110396882282073697349781407701150027357134841184256|33554944"
def inputClause14526 : CNF.NClause := [(25,true),(10,true),(909,false)]
theorem inputList14526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14526 = (containClause5 25 10) := by decide
  rw [he]
  exact input_contain 25 10 (by decide) v hb
mask_input "14526|4327788799063369698118367518036104040602397294887907509272254128346512609744690048814426160231687683233172643784762398137404191207445999921156415311568401014033503715319849649510248592805285405106374515984066055406780647774220793764564147394699562815402300054714269682368512|33555456"
def inputClause14527 : CNF.NClause := [(25,true),(11,true),(910,false)]
theorem inputList14527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14527 = (containClause5 25 11) := by decide
  rw [he]
  exact input_contain 25 11 (by decide) v hb
mask_input "14527|8655577598126739396236735036072208081204794589775815018544508256693025219489380097628852320463375366466345287569524796274808382414891999842312830623136802028067007430639699299020497185610570810212749031968132110813561295548441587529128294789399125630804600109428539364737024|33556480"
def inputClause14528 : CNF.NClause := [(25,true),(12,true),(911,false)]
theorem inputList14528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14528 = (containClause5 25 12) := by decide
  rw [he]
  exact input_contain 25 12 (by decide) v hb
mask_input "14528|17311155196253478792473470072144416162409589179551630037089016513386050438978760195257704640926750732932690575139049592549616764829783999684625661246273604056134014861279398598040994371221141620425498063936264221627122591096883175058256589578798251261609200218857078729474048|33558528"
def inputClause14529 : CNF.NClause := [(25,true),(13,true),(912,false)]
theorem inputList14529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14529 = (containClause5 25 13) := by decide
  rw [he]
  exact input_contain 25 13 (by decide) v hb
mask_input "14529|34622310392506957584946940144288832324819178359103260074178033026772100877957520390515409281853501465865381150278099185099233529659567999369251322492547208112268029722558797196081988742442283240850996127872528443254245182193766350116513179157596502523218400437714157458948096|33562624"
def inputClause14530 : CNF.NClause := [(25,true),(14,true),(913,false)]
theorem inputList14530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14530 = (containClause5 25 14) := by decide
  rw [he]
  exact input_contain 25 14 (by decide) v hb
mask_input "14530|69244620785013915169893880288577664649638356718206520148356066053544201755915040781030818563707002931730762300556198370198467059319135998738502644985094416224536059445117594392163977484884566481701992255745056886508490364387532700233026358315193005046436800875428314917896192|33570816"
def inputClause14531 : CNF.NClause := [(25,true),(15,true),(914,false)]
theorem inputList14531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14531 = (containClause5 25 15) := by decide
  rw [he]
  exact input_contain 25 15 (by decide) v hb
mask_input "14531|138489241570027830339787760577155329299276713436413040296712132107088403511830081562061637127414005863461524601112396740396934118638271997477005289970188832449072118890235188784327954969769132963403984511490113773016980728775065400466052716630386010092873601750856629835792384|33587200"
def inputClause14532 : CNF.NClause := [(25,true),(16,true),(915,false)]
theorem inputList14532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14532 = (containClause5 25 16) := by decide
  rw [he]
  exact input_contain 25 16 (by decide) v hb
mask_input "14532|276978483140055660679575521154310658598553426872826080593424264214176807023660163124123274254828011726923049202224793480793868237276543994954010579940377664898144237780470377568655909939538265926807969022980227546033961457550130800932105433260772020185747203501713259671584768|33619968"
def inputClause14533 : CNF.NClause := [(25,true),(17,true),(916,false)]
theorem inputList14533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14533 = (containClause5 25 17) := by decide
  rw [he]
  exact input_contain 25 17 (by decide) v hb
mask_input "14533|553956966280111321359151042308621317197106853745652161186848528428353614047320326248246548509656023453846098404449586961587736474553087989908021159880755329796288475560940755137311819879076531853615938045960455092067922915100261601864210866521544040371494407003426519343169536|33685504"
def inputClause14534 : CNF.NClause := [(25,true),(18,true),(917,false)]
theorem inputList14534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14534 = (containClause5 25 18) := by decide
  rw [he]
  exact input_contain 25 18 (by decide) v hb
mask_input "14534|1107913932560222642718302084617242634394213707491304322373697056856707228094640652496493097019312046907692196808899173923175472949106175979816042319761510659592576951121881510274623639758153063707231876091920910184135845830200523203728421733043088080742988814006853038686339072|33816576"
def inputClause14535 : CNF.NClause := [(25,true),(19,true),(918,false)]
theorem inputList14535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14535 = (containClause5 25 19) := by decide
  rw [he]
  exact input_contain 25 19 (by decide) v hb
mask_input "14535|2215827865120445285436604169234485268788427414982608644747394113713414456189281304992986194038624093815384393617798347846350945898212351959632084639523021319185153902243763020549247279516306127414463752183841820368271691660401046407456843466086176161485977628013706077372678144|34078720"
def inputClause14536 : CNF.NClause := [(25,true),(20,true),(919,false)]
theorem inputList14536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14536 = (containClause5 25 20) := by decide
  rw [he]
  exact input_contain 25 20 (by decide) v hb
mask_input "14536|4431655730240890570873208338468970537576854829965217289494788227426828912378562609985972388077248187630768787235596695692701891796424703919264169279046042638370307804487526041098494559032612254828927504367683640736543383320802092814913686932172352322971955256027412154745356288|34603008"
def inputClause14537 : CNF.NClause := [(25,true),(21,true),(920,false)]
theorem inputList14537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14537 = (containClause5 25 21) := by decide
  rw [he]
  exact input_contain 25 21 (by decide) v hb
mask_input "14537|8863311460481781141746416676937941075153709659930434578989576454853657824757125219971944776154496375261537574471193391385403783592849407838528338558092085276740615608975052082196989118065224509657855008735367281473086766641604185629827373864344704645943910512054824309490712576|35651584"
def inputClause14538 : CNF.NClause := [(25,true),(22,true),(921,false)]
theorem inputList14538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14538 = (containClause5 25 22) := by decide
  rw [he]
  exact input_contain 25 22 (by decide) v hb
mask_input "14538|17726622920963562283492833353875882150307419319860869157979152909707315649514250439943889552308992750523075148942386782770807567185698815677056677116184170553481231217950104164393978236130449019315710017470734562946173533283208371259654747728689409291887821024109648618981425152|37748736"
def inputClause14539 : CNF.NClause := [(25,true),(23,true),(922,false)]
theorem inputList14539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14539 = (containClause5 25 23) := by decide
  rw [he]
  exact input_contain 25 23 (by decide) v hb
mask_input "14539|35453245841927124566985666707751764300614838639721738315958305819414631299028500879887779104617985501046150297884773565541615134371397631354113354232368341106962462435900208328787956472260898038631420034941469125892347066566416742519309495457378818583775642048219297237962850304|41943040"
def inputClause14540 : CNF.NClause := [(25,true),(24,true),(923,false)]
theorem inputList14540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14540 = (containClause5 25 24) := by decide
  rw [he]
  exact input_contain 25 24 (by decide) v hb
mask_input "14540|70906491683854249133971333415503528601229677279443476631916611638829262598057001759775558209235971002092300595769547131083230268742795262708226708464736682213924924871800416657575912944521796077262840069882938251784694133132833485038618990914757637167551284096438594475925700608|50331648"
def inputClause14541 : CNF.NClause := [(25,true),(26,true),(925,false)]
theorem inputList14541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14541 = (containClause5 25 26) := by decide
  rw [he]
  exact input_contain 25 26 (by decide) v hb
mask_input "14541|283625966735416996535885333662014114404918709117773906527666446555317050392228007039102232836943884008369202383078188524332921074971181050832906833858946728855699699487201666630303651778087184309051360279531753007138776532531333940154475963659030548670205136385754377903702802432|100663296"
def inputClause14542 : CNF.NClause := [(25,true),(27,true),(926,false)]
theorem inputList14542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14542 = (containClause5 25 27) := by decide
  rw [he]
  exact input_contain 25 27 (by decide) v hb
mask_input "14542|567251933470833993071770667324028228809837418235547813055332893110634100784456014078204465673887768016738404766156377048665842149942362101665813667717893457711399398974403333260607303556174368618102720559063506014277553065062667880308951927318061097340410272771508755807405604864|167772160"
end Percolation.MaskChain
