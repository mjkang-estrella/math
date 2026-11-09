import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14114 : CNF.NClause := [(11,true),(19,true),(484,false)]
theorem inputList14114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14114
  have he : decodeClause inputClause14114 = containClause5 11 19 := by decide
  rw [he]
  exact input_contain 11 19 (by decide) v hb
mask_input "14114|49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642816|526336"
def inputClause14116 : CNF.NClause := [(11,true),(21,true),(486,false)]
theorem inputList14116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14116
  have he : decodeClause inputClause14116 = containClause5 11 21 := by decide
  rw [he]
  exact input_contain 11 21 (by decide) v hb
mask_input "14116|199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264|2099200"
def inputClause14117 : CNF.NClause := [(11,true),(22,true),(487,false)]
theorem inputList14117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14117 = (containClause5 11 22) := by decide
  rw [he]
  exact input_contain 11 22 (by decide) v hb
mask_input "14117|399583814440447005616844445413525287135820562261116307309972090832047582568929999375399181192126972308457847183540047730617340886948900519205142528|4196352"
def inputClause14119 : CNF.NClause := [(11,true),(24,true),(489,false)]
theorem inputList14119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14119
  have he : decodeClause inputClause14119 = containClause5 11 24 := by decide
  rw [he]
  exact input_contain 11 24 (by decide) v hb
mask_input "14119|1598335257761788022467377781654101148543282249044465229239888363328190330275719997501596724768507889233831388734160190922469363547795602076820570112|16779264"
def inputClause14121 : CNF.NClause := [(11,true),(26,true),(491,false)]
theorem inputList14121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14121 = (containClause5 11 26) := by decide
  rw [he]
  exact input_contain 11 26 (by decide) v hb
mask_input "14121|6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408307282280448|67110912"
def inputClause14124 : CNF.NClause := [(11,true),(29,true),(494,false)]
theorem inputList14124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14124 = (containClause5 11 29) := by decide
  rw [he]
  exact input_contain 11 29 (by decide) v hb
mask_input "14124|51146728248377216718956089012931236753385031969422887335676427626502090568823039920051095192592252455482604439493126109519019633529459266458258243584|536872960"
def inputClause14127 : CNF.NClause := [(12,true),(1,true),(497,false)]
theorem inputList14127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14127 = (containClause5 12 1) := by decide
  rw [he]
  exact input_contain 12 1 (by decide) v hb
mask_input "14127|409173825987017733751648712103449894027080255755383098685411421012016724550584319360408761540738019643860835515945008876152157068235674131666065948672|4098"
def inputClause14128 : CNF.NClause := [(12,true),(2,true),(498,false)]
theorem inputList14128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14128 = (containClause5 12 2) := by decide
  rw [he]
  exact input_contain 12 2 (by decide) v hb
mask_input "14128|818347651974035467503297424206899788054160511510766197370822842024033449101168638720817523081476039287721671031890017752304314136471348263332131897344|4100"
def inputClause14131 : CNF.NClause := [(12,true),(5,true),(501,false)]
theorem inputList14131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14131 = (containClause5 12 5) := by decide
  rw [he]
  exact input_contain 12 5 (by decide) v hb
mask_input "14131|6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752|4128"
def inputClause14134 : CNF.NClause := [(12,true),(8,true),(504,false)]
theorem inputList14134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14134 = (containClause5 12 8) := by decide
  rw [he]
  exact input_contain 12 8 (by decide) v hb
mask_input "14134|52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016|4352"
def inputClause14136 : CNF.NClause := [(12,true),(10,true),(506,false)]
theorem inputList14136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14136 = (containClause5 12 10) := by decide
  rw [he]
  exact input_contain 12 10 (by decide) v hb
mask_input "14136|209496998905353079680844140596966345741865090946756146526930647558152562969899171512529285908857866057656747784163844544589904418936665155413025765720064|5120"
def inputClause14137 : CNF.NClause := [(12,true),(11,true),(507,false)]
theorem inputList14137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14137 = (containClause5 12 11) := by decide
  rw [he]
  exact input_contain 12 11 (by decide) v hb
mask_input "14137|418993997810706159361688281193932691483730181893512293053861295116305125939798343025058571817715732115313495568327689089179808837873330310826051531440128|6144"
def inputClause14157 : CNF.NClause := [(13,true),(1,true),(528,false)]
theorem inputList14157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14157 = (containClause5 13 1) := by decide
  rw [he]
  exact input_contain 13 1 (by decide) v hb
mask_input "14157|878694100496718043517683302282418331810487718418343092402491322775749527474899974671687634004666183037093927858109549828751614463963730408009475621262727315456|8194"
def inputClause14158 : CNF.NClause := [(13,true),(2,true),(529,false)]
theorem inputList14158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14158 = (containClause5 13 2) := by decide
  rw [he]
  exact input_contain 13 2 (by decide) v hb
mask_input "14158|1757388200993436087035366604564836663620975436836686184804982645551499054949799949343375268009332366074187855716219099657503228927927460816018951242525454630912|8196"
def inputClause14161 : CNF.NClause := [(13,true),(5,true),(532,false)]
theorem inputList14161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14161 = (containClause5 13 5) := by decide
  rw [he]
  exact input_contain 13 5 (by decide) v hb
mask_input "14161|14059105607947488696282932836518693308967803494693489478439861164411992439598399594747002144074658928593502845729752797260025831423419686528151609940203637047296|8224"
def inputClause14164 : CNF.NClause := [(13,true),(8,true),(535,false)]
theorem inputList14164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14164 = (containClause5 13 8) := by decide
  rw [he]
  exact input_contain 13 8 (by decide) v hb
mask_input "14164|112472844863579909570263462692149546471742427957547915827518889315295939516787196757976017152597271428748022765838022378080206651387357492225212879521629096378368|8448"
def inputClause14166 : CNF.NClause := [(13,true),(10,true),(537,false)]
theorem inputList14166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14166 = (containClause5 13 10) := by decide
  rw [he]
  exact input_contain 13 10 (by decide) v hb
mask_input "14166|449891379454319638281053850768598185886969711830191663310075557261183758067148787031904068610389085714992091063352089512320826605549429968900851518086516385513472|9216"
def inputClause14167 : CNF.NClause := [(13,true),(11,true),(538,false)]
theorem inputList14167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14167 = (containClause5 13 11) := by decide
  rw [he]
  exact input_contain 13 11 (by decide) v hb
mask_input "14167|899782758908639276562107701537196371773939423660383326620151114522367516134297574063808137220778171429984182126704179024641653211098859937801703036173032771026944|10240"
def inputClause14187 : CNF.NClause := [(14,true),(1,true),(559,false)]
theorem inputList14187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14187 = (containClause5 14 1) := by decide
  rw [he]
  exact input_contain 14 1 (by decide) v hb
mask_input "14187|1886981212410770676120777290494134445458460610208220214188103150122812081196074426043063362588829383770734187515381922449885292314962396316280717125716348021824697663488|16386"
def inputClause14188 : CNF.NClause := [(14,true),(2,true),(560,false)]
theorem inputList14188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14188 = (containClause5 14 2) := by decide
  rw [he]
  exact input_contain 14 2 (by decide) v hb
mask_input "14188|3773962424821541352241554580988268890916921220416440428376206300245624162392148852086126725177658767541468375030763844899770584629924792632561434251432696043649395326976|16388"
def inputClause14191 : CNF.NClause := [(14,true),(5,true),(563,false)]
theorem inputList14191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14191 = (containClause5 14 5) := by decide
  rw [he]
  exact input_contain 14 5 (by decide) v hb
mask_input "14191|30191699398572330817932436647906151127335369763331523427009650401964993299137190816689013801421270140331747000246110759198164677039398341060491474011461568349195162615808|16416"
def inputClause14194 : CNF.NClause := [(14,true),(8,true),(566,false)]
theorem inputList14194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14194 = (containClause5 14 8) := by decide
  rw [he]
  exact input_contain 14 8 (by decide) v hb
mask_input "14194|241533595188578646543459493183249209018682958106652187416077203215719946393097526533512110411370161122653976001968886073585317416315186728483931792091692546793561300926464|16640"
def inputClause14196 : CNF.NClause := [(14,true),(10,true),(568,false)]
theorem inputList14196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14196 = (containClause5 14 10) := by decide
  rw [he]
  exact input_contain 14 10 (by decide) v hb
mask_input "14196|966134380754314586173837972732996836074731832426608749664308812862879785572390106134048441645480644490615904007875544294341269665260746913935727168366770187174245203705856|17408"
def inputClause14197 : CNF.NClause := [(14,true),(11,true),(569,false)]
theorem inputList14197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14197 = (containClause5 14 11) := by decide
  rw [he]
  exact input_contain 14 11 (by decide) v hb
mask_input "14197|1932268761508629172347675945465993672149463664853217499328617625725759571144780212268096883290961288981231808015751088588682539330521493827871454336733540374348490407411712|18432"
def inputClause14247 : CNF.NClause := [(16,true),(1,true),(621,false)]
theorem inputList14247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14247 = (containClause5 16 1) := by decide
  rw [he]
  exact input_contain 16 1 (by decide) v hb
mask_input "14247|8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500615833649152|65538"
def inputClause14248 : CNF.NClause := [(16,true),(2,true),(622,false)]
theorem inputList14248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14248 = (containClause5 16 2) := by decide
  rw [he]
  exact input_contain 16 2 (by decide) v hb
mask_input "14248|17404329748619824289860426352311291980336107281679382059399385520550823849520406290076876874227033232798165548605325345270876711736203910820971150664223534348495463082734165001231667298304|65540"
def inputClause14251 : CNF.NClause := [(16,true),(5,true),(625,false)]
theorem inputList14251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14251 = (containClause5 16 5) := by decide
  rw [he]
  exact input_contain 16 5 (by decide) v hb
mask_input "14251|139234637988958594318883410818490335842688858253435056475195084164406590796163250320615014993816265862385324388842602762167013693889631286567769205313788274787963704661873320009853338386432|65568"
def inputClause14254 : CNF.NClause := [(16,true),(8,true),(628,false)]
theorem inputList14254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14254 = (containClause5 16 8) := by decide
  rw [he]
  exact input_contain 16 8 (by decide) v hb
mask_input "14254|1113877103911668754551067286547922686741510866027480451801560673315252726369306002564920119950530126899082595110740822097336109551117050292542153642510306198303709637294986560078826707091456|65792"
def inputClause14256 : CNF.NClause := [(16,true),(10,true),(630,false)]
theorem inputList14256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14256 = (containClause5 16 10) := by decide
  rw [he]
  exact input_contain 16 10 (by decide) v hb
mask_input "14256|4455508415646675018204269146191690746966043464109921807206242693261010905477224010259680479802120507596330380442963288389344438204468201170168614570041224793214838549179946240315306828365824|66560"
def inputClause14257 : CNF.NClause := [(16,true),(11,true),(631,false)]
theorem inputList14257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14257 = (containClause5 16 11) := by decide
  rw [he]
  exact input_contain 16 11 (by decide) v hb
mask_input "14257|8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630613656731648|67584"
def inputClause14307 : CNF.NClause := [(18,true),(1,true),(683,false)]
theorem inputList14307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14307 = (containClause5 18 1) := by decide
  rw [he]
  exact input_contain 18 1 (by decide) v hb
mask_input "14307|40131652080904949243476790488282231640246122763238325954424140190648896440865179612073261537762363061729301215028215161995082338334532195000669973530974432754174985283877903733762083113741475809259744657408|262146"
def inputClause14308 : CNF.NClause := [(18,true),(2,true),(684,false)]
theorem inputList14308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14308
  have he : decodeClause inputClause14308 = containClause5 18 2 := by decide
  rw [he]
  exact input_contain 18 2 (by decide) v hb
mask_input "14308|80263304161809898486953580976564463280492245526476651908848280381297792881730359224146523075524726123458602430056430323990164676669064390001339947061948865508349970567755807467524166227482951618519489314816|262148"
def inputClause14311 : CNF.NClause := [(18,true),(5,true),(687,false)]
theorem inputList14311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14311 = (containClause5 18 5) := by decide
  rw [he]
  exact input_contain 18 5 (by decide) v hb
mask_input "14311|642106433294479187895628647812515706243937964211813215270786243050382343053842873793172184604197808987668819440451442591921317413352515120010719576495590924066799764542046459740193329819863612948155914518528|262176"
def inputClause14314 : CNF.NClause := [(18,true),(8,true),(690,false)]
theorem inputList14314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14314 = (containClause5 18 8) := by decide
  rw [he]
  exact input_contain 18 8 (by decide) v hb
mask_input "14314|5136851466355833503165029182500125649951503713694505722166289944403058744430742990345377476833582471901350555523611540735370539306820120960085756611964727392534398116336371677921546638558908903585247316148224|262400"
def inputClause14316 : CNF.NClause := [(18,true),(10,true),(692,false)]
theorem inputList14316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14316
  have he : decodeClause inputClause14316 = containClause5 18 10 := by decide
  rw [he]
  exact input_contain 18 10 (by decide) v hb
mask_input "14316|20547405865423334012660116730000502599806014854778022888665159777612234977722971961381509907334329887605402222094446162941482157227280483840343026447858909570137592465345486711686186554235635614340989264592896|263168"
def inputClause14317 : CNF.NClause := [(18,true),(11,true),(693,false)]
theorem inputList14317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14317 = (containClause5 18 11) := by decide
  rw [he]
  exact input_contain 18 11 (by decide) v hb
mask_input "14317|41094811730846668025320233460001005199612029709556045777330319555224469955445943922763019814668659775210804444188892325882964314454560967680686052895717819140275184930690973423372373108471271228681978529185792|264192"
def inputClause14337 : CNF.NClause := [(19,true),(1,true),(714,false)]
theorem inputList14337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14337 = (containClause5 19 1) := by decide
  rw [he]
  exact input_contain 19 1 (by decide) v hb
mask_input "14337|86182066610968551542636378241108028056376767329454880514019834315878107616003372189510312530372009184902888961739623919010110377987011442493486117202360415845666384627768436296772219009176743399772868636439042064384|524290"
def inputClause14338 : CNF.NClause := [(19,true),(2,true),(715,false)]
theorem inputList14338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14338 = (containClause5 19 2) := by decide
  rw [he]
  exact input_contain 19 2 (by decide) v hb
mask_input "14338|172364133221937103085272756482216056112753534658909761028039668631756215232006744379020625060744018369805777923479247838020220755974022884986972234404720831691332769255536872593544438018353486799545737272878084128768|524292"
def inputClause14341 : CNF.NClause := [(19,true),(5,true),(718,false)]
theorem inputList14341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14341 = (containClause5 19 5) := by decide
  rw [he]
  exact input_contain 19 5 (by decide) v hb
mask_input "14341|1378913065775496824682182051857728448902028277271278088224317349054049721856053955032165000485952146958446223387833982704161766047792183079895777875237766653530662154044294980748355504146827894396365898183024673030144|524320"
def inputClause14344 : CNF.NClause := [(19,true),(8,true),(721,false)]
theorem inputList14344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14344 = (containClause5 19 8) := by decide
  rw [he]
  exact input_contain 19 8 (by decide) v hb
mask_input "14344|11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787102671861633294128382337464639166223001902133228245297232354359845986844033174623155170927185464197384241152|524544"
end Percolation.MaskChain
