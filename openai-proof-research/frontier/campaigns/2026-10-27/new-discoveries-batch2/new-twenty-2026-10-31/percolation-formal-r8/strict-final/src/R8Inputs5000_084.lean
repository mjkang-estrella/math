import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause13755 : CNF.NClause := [(20,true),(764,true)]
theorem inputList13755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13755 = (omitClause5 20) := by decide
  rw [he]
  exact input_omit 20 v hb
mask_input "13755|0|97032380768794308446811218028906409703555376069793538196190752376628184542898555395679900551790404871905483168570692075385723752757175899465267954690073821200278436001303119096891580351974902801578937449607279296930802928364552192"
def inputClause13756 : CNF.NClause := [(21,true),(796,true)]
theorem inputList13756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13756
  have he : decodeClause inputClause13756 = omitClause5 21 := by decide
  rw [he]
  exact input_omit 21 v hb
mask_input "13756|0|416750902054990892129990736920078612321547395144744260024766113235252327363602004470089512554472143171433119412089577527868050103382460317522709753270676877880947348719625909903942392869488376545560313508492912623855671752342278830699839488"
def inputClause13757 : CNF.NClause := [(22,true),(828,true)]
theorem inputList13757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13757
  have he : decodeClause inputClause13757 = omitClause5 22 := by decide
  rw [he]
  exact input_omit 22 v hb
mask_input "13757|0|1789931494904685075276173995854677405670108698260665783090090606394441500334556509959080266614039273464334969326187482504649803797317086043777814127597786226282054644248700756391675078842436173515315000514484077967245659600421098975959924194158837760"
def inputClause13758 : CNF.NClause := [(23,true),(860,true)]
theorem inputList13758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13758 = (omitClause5 23) := by decide
  rw [he]
  exact input_omit 23 v hb
mask_input "13758|0|7687697232696013035490465480201479025983241823794691621558168976140934720122093268938148043346259333988919315645138393722043075242293497100043735968399262883880680368733084239192707430286484902215659282347932289182034267181757047930126964620533348010068803584"
def inputClause13759 : CNF.NClause := [(24,true),(892,true)]
theorem inputList13759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13759 = (omitClause5 24) := by decide
  rw [he]
  exact input_omit 24 v hb
mask_input "13759|0|33018408195979077897021236557282287907427957877257595132997544314167118909795303717151078492978574243417149687078570542430146722468917846078158686153933723556774167749937817760545719854776652565814014556763199275259251768296972608677399806172939779780596161306125402112"
def inputClause13761 : CNF.NClause := [(26,true),(956,true)]
theorem inputList13761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13761 = (omitClause5 26) := by decide
  rw [he]
  exact input_omit 26 v hb
mask_input "13761|0|609082125712499942522086399242199269429764178599687970429244153575809293172901631404100941617625641201581557264463041761466198116575193377911124206019540838720704856247279564366924353468128353022049974592451148679605349870337179684109147725966810350801733675194017346692614286874561740800"
def inputClause13762 : CNF.NClause := [(27,true),(988,true)]
theorem inputList13762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13762 = (omitClause5 27) := by decide
  rw [he]
  exact input_omit 27 v hb
mask_input "13762|0|2615987810513347951534240842431645045315929716077962908798218721607302370910488580305660104530507466131822931927619987366179553920147251083004047259447894239241837835650447017925067042251555454560047407752208612056538559879736027236124400377460220438127733515060190958901472126868316500692811382784"
def inputClause13763 : CNF.NClause := [(28,true),(1020,true)]
theorem inputList13763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13763
  have he : decodeClause inputClause13763 = omitClause5 28 := by decide
  rw [he]
  exact input_omit 28 v hb
mask_input "13763|0|11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601782444032"
def inputClause13764 : CNF.NClause := [(29,true),(1052,true)]
theorem inputList13764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13764 = (omitClause5 29) := by decide
  rw [he]
  exact input_omit 29 v hb
mask_input "13764|0|48256457640483526790736996345261885416402018013988046254372920519692978755949818346967788625106125949665803400115206697318508323999832505432847356782135608177546840733663168278805472312472633443174306792848764674320699568611310171751523817932405366025164140823449795139392236379439950593039113881265164914920320401408"
def inputClause13809 : CNF.NClause := [(1,true),(14,true),(169,false)]
theorem inputList13809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13809 = (containClause5 1 14) := by decide
  rw [he]
  exact input_contain 1 14 (by decide) v hb
mask_input "13809|748288838313422294120286634350736906063837462003712|16386"
def inputClause13812 : CNF.NClause := [(1,true),(17,true),(172,false)]
theorem inputList13812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13812 = (containClause5 1 17) := by decide
  rw [he]
  exact input_contain 1 17 (by decide) v hb
mask_input "13812|5986310706507378352962293074805895248510699696029696|131074"
def inputClause13813 : CNF.NClause := [(1,true),(18,true),(173,false)]
theorem inputList13813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13813 = (containClause5 1 18) := by decide
  rw [he]
  exact input_contain 1 18 (by decide) v hb
mask_input "13813|11972621413014756705924586149611790497021399392059392|262146"
def inputClause13814 : CNF.NClause := [(1,true),(19,true),(174,false)]
theorem inputList13814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13814 = (containClause5 1 19) := by decide
  rw [he]
  exact input_contain 1 19 (by decide) v hb
mask_input "13814|23945242826029513411849172299223580994042798784118784|524290"
def inputClause13817 : CNF.NClause := [(1,true),(22,true),(177,false)]
theorem inputList13817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13817 = (containClause5 1 22) := by decide
  rw [he]
  exact input_contain 1 22 (by decide) v hb
mask_input "13817|191561942608236107294793378393788647952342390272950272|4194306"
def inputClause13824 : CNF.NClause := [(1,true),(29,true),(184,false)]
theorem inputList13824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13824 = (containClause5 1 29) := by decide
  rw [he]
  exact input_contain 1 29 (by decide) v hb
mask_input "13824|24519928653854221733733552434404946937899825954937634816|536870914"
def inputClause13861 : CNF.NClause := [(3,true),(6,true),(223,false)]
theorem inputList13861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13861 = (containClause5 3 6) := by decide
  rw [he]
  exact input_contain 3 6 (by decide) v hb
mask_input "13861|13479973333575319897333507543509815336818572211270286240551805124608|72"
def inputClause13862 : CNF.NClause := [(3,true),(7,true),(224,false)]
theorem inputList13862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13862 = (containClause5 3 7) := by decide
  rw [he]
  exact input_contain 3 7 (by decide) v hb
mask_input "13862|26959946667150639794667015087019630673637144422540572481103610249216|136"
def inputClause13864 : CNF.NClause := [(3,true),(9,true),(226,false)]
theorem inputList13864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13864
  have he : decodeClause inputClause13864 = containClause5 3 9 := by decide
  rw [he]
  exact input_contain 3 9 (by decide) v hb
mask_input "13864|107839786668602559178668060348078522694548577690162289924414440996864|520"
def inputClause13867 : CNF.NClause := [(3,true),(12,true),(229,false)]
theorem inputList13867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13867 = (containClause5 3 12) := by decide
  rw [he]
  exact input_contain 3 12 (by decide) v hb
mask_input "13867|862718293348820473429344482784628181556388621521298319395315527974912|4104"
def inputClause13868 : CNF.NClause := [(3,true),(13,true),(230,false)]
theorem inputList13868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13868
  have he : decodeClause inputClause13868 = containClause5 3 13 := by decide
  rw [he]
  exact input_contain 3 13 (by decide) v hb
mask_input "13868|1725436586697640946858688965569256363112777243042596638790631055949824|8200"
def inputClause13869 : CNF.NClause := [(3,true),(14,true),(231,false)]
theorem inputList13869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13869
  have he : decodeClause inputClause13869 = containClause5 3 14 := by decide
  rw [he]
  exact input_contain 3 14 (by decide) v hb
mask_input "13869|3450873173395281893717377931138512726225554486085193277581262111899648|16392"
def inputClause13870 : CNF.NClause := [(3,true),(15,true),(232,false)]
theorem inputList13870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13870 = (containClause5 3 15) := by decide
  rw [he]
  exact input_contain 3 15 (by decide) v hb
mask_input "13870|6901746346790563787434755862277025452451108972170386555162524223799296|32776"
def inputClause13871 : CNF.NClause := [(3,true),(16,true),(233,false)]
theorem inputList13871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13871
  have he : decodeClause inputClause13871 = containClause5 3 16 := by decide
  rw [he]
  exact input_contain 3 16 (by decide) v hb
mask_input "13871|13803492693581127574869511724554050904902217944340773110325048447598592|65544"
def inputClause13872 : CNF.NClause := [(3,true),(17,true),(234,false)]
theorem inputList13872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13872 = (containClause5 3 17) := by decide
  rw [he]
  exact input_contain 3 17 (by decide) v hb
mask_input "13872|27606985387162255149739023449108101809804435888681546220650096895197184|131080"
def inputClause13873 : CNF.NClause := [(3,true),(18,true),(235,false)]
theorem inputList13873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13873
  have he : decodeClause inputClause13873 = containClause5 3 18 := by decide
  rw [he]
  exact input_contain 3 18 (by decide) v hb
mask_input "13873|55213970774324510299478046898216203619608871777363092441300193790394368|262152"
def inputClause13874 : CNF.NClause := [(3,true),(19,true),(236,false)]
theorem inputList13874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13874 = (containClause5 3 19) := by decide
  rw [he]
  exact input_contain 3 19 (by decide) v hb
mask_input "13874|110427941548649020598956093796432407239217743554726184882600387580788736|524296"
def inputClause13875 : CNF.NClause := [(3,true),(20,true),(237,false)]
theorem inputList13875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13875 = (containClause5 3 20) := by decide
  rw [he]
  exact input_contain 3 20 (by decide) v hb
mask_input "13875|220855883097298041197912187592864814478435487109452369765200775161577472|1048584"
def inputClause13876 : CNF.NClause := [(3,true),(21,true),(238,false)]
theorem inputList13876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13876
  have he : decodeClause inputClause13876 = containClause5 3 21 := by decide
  rw [he]
  exact input_contain 3 21 (by decide) v hb
mask_input "13876|441711766194596082395824375185729628956870974218904739530401550323154944|2097160"
def inputClause13877 : CNF.NClause := [(3,true),(22,true),(239,false)]
theorem inputList13877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13877
  have he : decodeClause inputClause13877 = containClause5 3 22 := by decide
  rw [he]
  exact input_contain 3 22 (by decide) v hb
mask_input "13877|883423532389192164791648750371459257913741948437809479060803100646309888|4194312"
def inputClause13878 : CNF.NClause := [(3,true),(23,true),(240,false)]
theorem inputList13878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13878 = (containClause5 3 23) := by decide
  rw [he]
  exact input_contain 3 23 (by decide) v hb
mask_input "13878|1766847064778384329583297500742918515827483896875618958121606201292619776|8388616"
def inputClause13879 : CNF.NClause := [(3,true),(24,true),(241,false)]
theorem inputList13879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13879 = (containClause5 3 24) := by decide
  rw [he]
  exact input_contain 3 24 (by decide) v hb
mask_input "13879|3533694129556768659166595001485837031654967793751237916243212402585239552|16777224"
def inputClause13881 : CNF.NClause := [(3,true),(26,true),(243,false)]
theorem inputList13881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13881 = (containClause5 3 26) := by decide
  rw [he]
  exact input_contain 3 26 (by decide) v hb
mask_input "13881|14134776518227074636666380005943348126619871175004951664972849610340958208|67108872"
def inputClause13882 : CNF.NClause := [(3,true),(27,true),(244,false)]
theorem inputList13882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13882 = (containClause5 3 27) := by decide
  rw [he]
  exact input_contain 3 27 (by decide) v hb
mask_input "13882|28269553036454149273332760011886696253239742350009903329945699220681916416|134217736"
def inputClause13883 : CNF.NClause := [(3,true),(28,true),(245,false)]
theorem inputList13883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13883
  have he : decodeClause inputClause13883 = containClause5 3 28 := by decide
  rw [he]
  exact input_contain 3 28 (by decide) v hb
mask_input "13883|56539106072908298546665520023773392506479484700019806659891398441363832832|268435464"
def inputClause13884 : CNF.NClause := [(3,true),(29,true),(246,false)]
theorem inputList13884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13884
  have he : decodeClause inputClause13884 = containClause5 3 29 := by decide
  rw [he]
  exact input_contain 3 29 (by decide) v hb
mask_input "13884|113078212145816597093331040047546785012958969400039613319782796882727665664|536870920"
def inputClause13949 : CNF.NClause := [(6,true),(3,true),(313,false)]
theorem inputList13949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13949 = (containClause5 6 3) := by decide
  rw [he]
  exact input_contain 6 3 (by decide) v hb
mask_input "13949|16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192|72"
def inputClause13952 : CNF.NClause := [(6,true),(7,true),(317,false)]
theorem inputList13952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13952 = (containClause5 6 7) := by decide
  rw [he]
  exact input_contain 6 7 (by decide) v hb
mask_input "13952|266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072|192"
def inputClause13954 : CNF.NClause := [(6,true),(9,true),(319,false)]
theorem inputList13954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13954 = (containClause5 6 9) := by decide
  rw [he]
  exact input_contain 6 9 (by decide) v hb
mask_input "13954|1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288|576"
def inputClause13957 : CNF.NClause := [(6,true),(12,true),(322,false)]
theorem inputList13957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13957 = (containClause5 6 12) := by decide
  rw [he]
  exact input_contain 6 12 (by decide) v hb
mask_input "13957|8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304|4160"
def inputClause13958 : CNF.NClause := [(6,true),(13,true),(323,false)]
theorem inputList13958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13958 = (containClause5 6 13) := by decide
  rw [he]
  exact input_contain 6 13 (by decide) v hb
mask_input "13958|17087896287367280659160173649356416916821636178853222159576332862577757806245124400183696695492608|8256"
end Percolation.MaskChain
