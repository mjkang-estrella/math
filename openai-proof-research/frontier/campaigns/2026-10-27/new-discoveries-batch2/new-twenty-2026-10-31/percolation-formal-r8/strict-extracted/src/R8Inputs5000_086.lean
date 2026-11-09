import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14050 : CNF.NClause := [(9,true),(15,true),(418,false)]
theorem inputList14050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14050
  have he : decodeClause inputClause14050 = containClause5 9 15 := by decide
  rw [he]
  exact input_contain 9 15 (by decide) v hb
mask_input "14050|676921312041214565326761275425557544784286395355423968547480366360991530225982818124993751490268451683933401113623918903558144|33280"
def inputClause14051 : CNF.NClause := [(9,true),(16,true),(419,false)]
theorem inputList14051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14051
  have he : decodeClause inputClause14051 = containClause5 9 16 := by decide
  rw [he]
  exact input_contain 9 16 (by decide) v hb
mask_input "14051|1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288|66048"
def inputClause14052 : CNF.NClause := [(9,true),(17,true),(420,false)]
theorem inputList14052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14052
  have he : decodeClause inputClause14052 = containClause5 9 17 := by decide
  rw [he]
  exact input_contain 9 17 (by decide) v hb
mask_input "14052|2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576|131584"
def inputClause14053 : CNF.NClause := [(9,true),(18,true),(421,false)]
theorem inputList14053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14053 = (containClause5 9 18) := by decide
  rw [he]
  exact input_contain 9 18 (by decide) v hb
mask_input "14053|5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152|262656"
def inputClause14054 : CNF.NClause := [(9,true),(19,true),(422,false)]
theorem inputList14054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14054 = (containClause5 9 19) := by decide
  rw [he]
  exact input_contain 9 19 (by decide) v hb
mask_input "14054|10830740992659433045228180406808920716548582325686783496759685861775864483615725089999900023844295226942934417817982702456930304|524800"
def inputClause14055 : CNF.NClause := [(9,true),(20,true),(423,false)]
theorem inputList14055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14055
  have he : decodeClause inputClause14055 = containClause5 9 20 := by decide
  rw [he]
  exact input_contain 9 20 (by decide) v hb
mask_input "14055|21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608|1049088"
def inputClause14056 : CNF.NClause := [(9,true),(21,true),(424,false)]
theorem inputList14056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14056
  have he : decodeClause inputClause14056 = containClause5 9 21 := by decide
  rw [he]
  exact input_contain 9 21 (by decide) v hb
mask_input "14056|43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216|2097664"
def inputClause14057 : CNF.NClause := [(9,true),(22,true),(425,false)]
theorem inputList14057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14057
  have he : decodeClause inputClause14057 = containClause5 9 22 := by decide
  rw [he]
  exact input_contain 9 22 (by decide) v hb
mask_input "14057|86645927941275464361825443254471365732388658605494267974077486894206915868925800719999200190754361815543475342543861619655442432|4194816"
def inputClause14058 : CNF.NClause := [(9,true),(23,true),(426,false)]
theorem inputList14058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14058
  have he : decodeClause inputClause14058 = containClause5 9 23 := by decide
  rw [he]
  exact input_contain 9 23 (by decide) v hb
mask_input "14058|173291855882550928723650886508942731464777317210988535948154973788413831737851601439998400381508723631086950685087723239310884864|8389120"
def inputClause14059 : CNF.NClause := [(9,true),(24,true),(427,false)]
theorem inputList14059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14059
  have he : decodeClause inputClause14059 = containClause5 9 24 := by decide
  rw [he]
  exact input_contain 9 24 (by decide) v hb
mask_input "14059|346583711765101857447301773017885462929554634421977071896309947576827663475703202879996800763017447262173901370175446478621769728|16777728"
def inputClause14061 : CNF.NClause := [(9,true),(26,true),(429,false)]
theorem inputList14061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14061 = (containClause5 9 26) := by decide
  rw [he]
  exact input_contain 9 26 (by decide) v hb
mask_input "14061|1386334847060407429789207092071541851718218537687908287585239790307310653902812811519987203052069789048695605480701785914487078912|67109376"
def inputClause14062 : CNF.NClause := [(9,true),(27,true),(430,false)]
theorem inputList14062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14062 = (containClause5 9 27) := by decide
  rw [he]
  exact input_contain 9 27 (by decide) v hb
mask_input "14062|2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824|134218240"
def inputClause14063 : CNF.NClause := [(9,true),(28,true),(431,false)]
theorem inputList14063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14063
  have he : decodeClause inputClause14063 = containClause5 9 28 := by decide
  rw [he]
  exact input_contain 9 28 (by decide) v hb
mask_input "14063|5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648|268435968"
def inputClause14064 : CNF.NClause := [(9,true),(29,true),(432,false)]
theorem inputList14064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14064
  have he : decodeClause inputClause14064 = containClause5 9 29 := by decide
  rw [he]
  exact input_contain 9 29 (by decide) v hb
mask_input "14064|11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296|536871424"
def inputClause14129 : CNF.NClause := [(12,true),(3,true),(499,false)]
theorem inputList14129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14129 = (containClause5 12 3) := by decide
  rw [he]
  exact input_contain 12 3 (by decide) v hb
mask_input "14129|1636695303948070935006594848413799576108321023021532394741645684048066898202337277441635046162952078575443342063780035504608628272942696526664263794688|4104"
def inputClause14132 : CNF.NClause := [(12,true),(6,true),(502,false)]
theorem inputList14132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14132 = (containClause5 12 6) := by decide
  rw [he]
  exact input_contain 12 6 (by decide) v hb
mask_input "14132|13093562431584567480052758787310396608866568184172259157933165472384535185618698219533080369303616628603546736510240284036869026183541572213314110357504|4160"
def inputClause14133 : CNF.NClause := [(12,true),(7,true),(503,false)]
theorem inputList14133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14133 = (containClause5 12 7) := by decide
  rw [he]
  exact input_contain 12 7 (by decide) v hb
mask_input "14133|26187124863169134960105517574620793217733136368344518315866330944769070371237396439066160738607233257207093473020480568073738052367083144426628220715008|4224"
def inputClause14135 : CNF.NClause := [(12,true),(9,true),(505,false)]
theorem inputList14135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14135 = (containClause5 12 9) := by decide
  rw [he]
  exact input_contain 12 9 (by decide) v hb
mask_input "14135|104748499452676539840422070298483172870932545473378073263465323779076281484949585756264642954428933028828373892081922272294952209468332577706512882860032|4608"
def inputClause14138 : CNF.NClause := [(12,true),(13,true),(509,false)]
theorem inputList14138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14138 = (containClause5 12 13) := by decide
  rw [he]
  exact input_contain 12 13 (by decide) v hb
mask_input "14138|1675975991242824637446753124775730765934920727574049172215445180465220503759193372100234287270862928461253982273310756356719235351493321243304206125760512|12288"
def inputClause14140 : CNF.NClause := [(12,true),(15,true),(511,false)]
theorem inputList14140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14140 = (containClause5 12 15) := by decide
  rw [he]
  exact input_contain 12 15 (by decide) v hb
mask_input "14140|6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048|36864"
def inputClause14141 : CNF.NClause := [(12,true),(16,true),(512,false)]
theorem inputList14141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14141 = (containClause5 12 16) := by decide
  rw [he]
  exact input_contain 12 16 (by decide) v hb
mask_input "14141|13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096|69632"
def inputClause14142 : CNF.NClause := [(12,true),(17,true),(513,false)]
theorem inputList14142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14142 = (containClause5 12 17) := by decide
  rw [he]
  exact input_contain 12 17 (by decide) v hb
mask_input "14142|26815615859885194199148049996411692254958731641184786755447122887443528060147093953603748596333806855380063716372972101707507765623893139892867298012168192|135168"
def inputClause14143 : CNF.NClause := [(12,true),(18,true),(514,false)]
theorem inputList14143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14143 = (containClause5 12 18) := by decide
  rw [he]
  exact input_contain 12 18 (by decide) v hb
mask_input "14143|53631231719770388398296099992823384509917463282369573510894245774887056120294187907207497192667613710760127432745944203415015531247786279785734596024336384|266240"
def inputClause14144 : CNF.NClause := [(12,true),(19,true),(515,false)]
theorem inputList14144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14144 = (containClause5 12 19) := by decide
  rw [he]
  exact input_contain 12 19 (by decide) v hb
mask_input "14144|107262463439540776796592199985646769019834926564739147021788491549774112240588375814414994385335227421520254865491888406830031062495572559571469192048672768|528384"
def inputClause14145 : CNF.NClause := [(12,true),(20,true),(516,false)]
theorem inputList14145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14145 = (containClause5 12 20) := by decide
  rw [he]
  exact input_contain 12 20 (by decide) v hb
mask_input "14145|214524926879081553593184399971293538039669853129478294043576983099548224481176751628829988770670454843040509730983776813660062124991145119142938384097345536|1052672"
def inputClause14146 : CNF.NClause := [(12,true),(21,true),(517,false)]
theorem inputList14146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14146 = (containClause5 12 21) := by decide
  rw [he]
  exact input_contain 12 21 (by decide) v hb
mask_input "14146|429049853758163107186368799942587076079339706258956588087153966199096448962353503257659977541340909686081019461967553627320124249982290238285876768194691072|2101248"
def inputClause14147 : CNF.NClause := [(12,true),(22,true),(518,false)]
theorem inputList14147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14147 = (containClause5 12 22) := by decide
  rw [he]
  exact input_contain 12 22 (by decide) v hb
mask_input "14147|858099707516326214372737599885174152158679412517913176174307932398192897924707006515319955082681819372162038923935107254640248499964580476571753536389382144|4198400"
def inputClause14148 : CNF.NClause := [(12,true),(23,true),(519,false)]
theorem inputList14148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14148 = (containClause5 12 23) := by decide
  rw [he]
  exact input_contain 12 23 (by decide) v hb
mask_input "14148|1716199415032652428745475199770348304317358825035826352348615864796385795849414013030639910165363638744324077847870214509280496999929160953143507072778764288|8392704"
def inputClause14149 : CNF.NClause := [(12,true),(24,true),(520,false)]
theorem inputList14149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14149 = (containClause5 12 24) := by decide
  rw [he]
  exact input_contain 12 24 (by decide) v hb
mask_input "14149|3432398830065304857490950399540696608634717650071652704697231729592771591698828026061279820330727277488648155695740429018560993999858321906287014145557528576|16781312"
def inputClause14151 : CNF.NClause := [(12,true),(26,true),(522,false)]
theorem inputList14151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14151 = (containClause5 12 26) := by decide
  rw [he]
  exact input_contain 12 26 (by decide) v hb
mask_input "14151|13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782961716074243975999433287625148056582230114304|67112960"
def inputClause14153 : CNF.NClause := [(12,true),(28,true),(524,false)]
theorem inputList14153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14153 = (containClause5 12 28) := by decide
  rw [he]
  exact input_contain 12 28 (by decide) v hb
mask_input "14153|54918381281044877719855206392651145738155482401146443275155707673484345467181248416980477125291636439818370491131846864296975903997733150500592226328920457216|268439552"
def inputClause14154 : CNF.NClause := [(12,true),(29,true),(525,false)]
theorem inputList14154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14154 = (containClause5 12 29) := by decide
  rw [he]
  exact input_contain 12 29 (by decide) v hb
mask_input "14154|109836762562089755439710412785302291476310964802292886550311415346968690934362496833960954250583272879636740982263693728593951807995466301001184452657840914432|536875008"
def inputClause14159 : CNF.NClause := [(13,true),(3,true),(530,false)]
theorem inputList14159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14159 = (containClause5 13 3) := by decide
  rw [he]
  exact input_contain 13 3 (by decide) v hb
mask_input "14159|3514776401986872174070733209129673327241950873673372369609965291102998109899599898686750536018664732148375711432438199315006457855854921632037902485050909261824|8200"
def inputClause14162 : CNF.NClause := [(13,true),(6,true),(533,false)]
theorem inputList14162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14162 = (containClause5 13 6) := by decide
  rw [he]
  exact input_contain 13 6 (by decide) v hb
mask_input "14162|28118211215894977392565865673037386617935606989386978956879722328823984879196799189494004288149317857187005691459505594520051662846839373056303219880407274094592|8256"
def inputClause14163 : CNF.NClause := [(13,true),(7,true),(534,false)]
theorem inputList14163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14163 = (containClause5 13 7) := by decide
  rw [he]
  exact input_contain 13 7 (by decide) v hb
mask_input "14163|56236422431789954785131731346074773235871213978773957913759444657647969758393598378988008576298635714374011382919011189040103325693678746112606439760814548189184|8320"
def inputClause14165 : CNF.NClause := [(13,true),(9,true),(536,false)]
theorem inputList14165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14165 = (containClause5 13 9) := by decide
  rw [he]
  exact input_contain 13 9 (by decide) v hb
mask_input "14165|224945689727159819140526925384299092943484855915095831655037778630591879033574393515952034305194542857496045531676044756160413302774714984450425759043258192756736|8704"
def inputClause14168 : CNF.NClause := [(13,true),(12,true),(539,false)]
theorem inputList14168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14168 = (containClause5 13 12) := by decide
  rw [he]
  exact input_contain 13 12 (by decide) v hb
mask_input "14168|1799565517817278553124215403074392743547878847320766653240302229044735032268595148127616274441556342859968364253408358049283306422197719875603406072346065542053888|12288"
def inputClause14170 : CNF.NClause := [(13,true),(15,true),(542,false)]
theorem inputList14170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14170 = (containClause5 13 15) := by decide
  rw [he]
  exact input_contain 13 15 (by decide) v hb
mask_input "14170|14396524142538228424993723224595141948383030778566133225922417832357880258148761185020930195532450742879746914027266864394266451377581759004827248578768524336431104|40960"
def inputClause14171 : CNF.NClause := [(13,true),(16,true),(543,false)]
theorem inputList14171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14171 = (containClause5 13 16) := by decide
  rw [he]
  exact input_contain 13 16 (by decide) v hb
mask_input "14171|28793048285076456849987446449190283896766061557132266451844835664715760516297522370041860391064901485759493828054533728788532902755163518009654497157537048672862208|73728"
def inputClause14173 : CNF.NClause := [(13,true),(18,true),(545,false)]
theorem inputList14173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14173 = (containClause5 13 18) := by decide
  rw [he]
  exact input_contain 13 18 (by decide) v hb
mask_input "14173|115172193140305827399949785796761135587064246228529065807379342658863042065190089480167441564259605943037975312218134915154131611020654072038617988630148194691448832|270336"
end Percolation.MaskChain
