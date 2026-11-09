import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14000 : CNF.NClause := [(7,true),(25,true),(366,false)]
theorem inputList14000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14000
  have he : decodeClause inputClause14000 = containClause5 7 25 := by decide
  rw [he]
  exact input_contain 7 25 (by decide) v hb
mask_input "14000|150306725297525326584926758194517569752043683130132471725266622178061377607334940381676735896625196994043838464|33554560"
def inputClause14005 : CNF.NClause := [(7,true),(30,true),(371,false)]
theorem inputList14005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14005
  have he : decodeClause inputClause14005 = containClause5 7 30 := by decide
  rw [he]
  exact input_contain 7 30 (by decide) v hb
mask_input "14005|4809815209520810450717656262224562232065397860164239095208531909697964083434718092213655548692006303809402830848|1073741952"
def inputClause14006 : CNF.NClause := [(8,true),(0,true),(372,false)]
theorem inputList14006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14006
  have he : decodeClause inputClause14006 = containClause5 8 0 := by decide
  rw [he]
  exact input_contain 8 0 (by decide) v hb
mask_input "14006|9619630419041620901435312524449124464130795720328478190417063819395928166869436184427311097384012607618805661696|257"
def inputClause14030 : CNF.NClause := [(8,true),(25,true),(397,false)]
theorem inputList14030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14030
  have he : decodeClause inputClause14030 = containClause5 8 25 := by decide
  rw [he]
  exact input_contain 8 25 (by decide) v hb
mask_input "14030|322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672|33554688"
def inputClause14035 : CNF.NClause := [(8,true),(30,true),(402,false)]
theorem inputList14035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14035 = (containClause5 8 30) := by decide
  rw [he]
  exact input_contain 8 30 (by decide) v hb
mask_input "14035|10328999512347634358623676688012047497318823171316894051322637426162590488067364778518581413120551325743612687890989973504|1073742080"
def inputClause14036 : CNF.NClause := [(9,true),(0,true),(403,false)]
theorem inputList14036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14036 = (containClause5 9 0) := by decide
  rw [he]
  exact input_contain 9 0 (by decide) v hb
mask_input "14036|20657999024695268717247353376024094994637646342633788102645274852325180976134729557037162826241102651487225375781979947008|513"
def inputClause14060 : CNF.NClause := [(9,true),(25,true),(428,false)]
theorem inputList14060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14060 = (containClause5 9 25) := by decide
  rw [he]
  exact input_contain 9 25 (by decide) v hb
mask_input "14060|693167423530203714894603546035770925859109268843954143792619895153655326951406405759993601526034894524347802740350892957243539456|33554944"
def inputClause14065 : CNF.NClause := [(9,true),(30,true),(433,false)]
theorem inputList14065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14065
  have he : decodeClause inputClause14065 = containClause5 9 30 := by decide
  rw [he]
  exact input_contain 9 30 (by decide) v hb
mask_input "14065|22181357552966518876627313473144669627491496603006532601363836644916970462445004984319795248833116624779129687691228574631793262592|1073742336"
def inputClause14066 : CNF.NClause := [(10,true),(0,true),(434,false)]
theorem inputList14066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14066
  have he : decodeClause inputClause14066 = containClause5 10 0 := by decide
  rw [he]
  exact input_contain 10 0 (by decide) v hb
mask_input "14066|44362715105933037753254626946289339254982993206013065202727673289833940924890009968639590497666233249558259375382457149263586525184|1025"
def inputClause14090 : CNF.NClause := [(10,true),(25,true),(459,false)]
theorem inputList14090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14090 = (containClause5 10 25) := by decide
  rw [he]
  exact input_contain 10 25 (by decide) v hb
mask_input "14090|1488565707357402911845015158554633286356257506687627387456491927921949262056238946972039271861787782268441644249633132407878864135402815488|33555456"
def inputClause14095 : CNF.NClause := [(10,true),(30,true),(464,false)]
theorem inputList14095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14095
  have he : decodeClause inputClause14095 = containClause5 10 30 := by decide
  rw [he]
  exact input_contain 10 30 (by decide) v hb
mask_input "14095|47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616|1073742848"
def inputClause14096 : CNF.NClause := [(11,true),(0,true),(465,false)]
theorem inputList14096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14096 = (containClause5 11 0) := by decide
  rw [he]
  exact input_contain 11 0 (by decide) v hb
mask_input "14096|95268205270873786358080970147496530326800480428008152797215483387004752771599292606210513399154418065180265231976520474104247304665780191232|2049"
def inputClause14120 : CNF.NClause := [(11,true),(25,true),(490,false)]
theorem inputList14120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14120 = (containClause5 11 25) := by decide
  rw [he]
  exact input_contain 11 25 (by decide) v hb
mask_input "14120|3196670515523576044934755563308202297086564498088930458479776726656380660551439995003193449537015778467662777468320381844938727095591204153641140224|33556480"
def inputClause14125 : CNF.NClause := [(11,true),(30,true),(495,false)]
theorem inputList14125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14125
  have he : decodeClause inputClause14125 = containClause5 11 30 := by decide
  rw [he]
  exact input_contain 11 30 (by decide) v hb
mask_input "14125|102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168|1073743872"
def inputClause14126 : CNF.NClause := [(12,true),(0,true),(496,false)]
theorem inputList14126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14126 = (containClause5 12 0) := by decide
  rw [he]
  exact input_contain 12 0 (by decide) v hb
mask_input "14126|204586912993508866875824356051724947013540127877691549342705710506008362275292159680204380770369009821930417757972504438076078534117837065833032974336|4097"
def inputClause14150 : CNF.NClause := [(12,true),(25,true),(521,false)]
theorem inputList14150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14150 = (containClause5 12 25) := by decide
  rw [he]
  exact input_contain 12 25 (by decide) v hb
mask_input "14150|6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152|33558528"
def inputClause14155 : CNF.NClause := [(12,true),(30,true),(526,false)]
theorem inputList14155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14155 = (containClause5 12 30) := by decide
  rw [he]
  exact input_contain 12 30 (by decide) v hb
mask_input "14155|219673525124179510879420825570604582952621929604585773100622830693937381868724993667921908501166545759273481964527387457187903615990932602002368905315681828864|1073745920"
def inputClause14156 : CNF.NClause := [(13,true),(0,true),(527,false)]
theorem inputList14156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14156 = (containClause5 13 0) := by decide
  rw [he]
  exact input_contain 13 0 (by decide) v hb
mask_input "14156|439347050248359021758841651141209165905243859209171546201245661387874763737449987335843817002333091518546963929054774914375807231981865204004737810631363657728|8193"
def inputClause14180 : CNF.NClause := [(13,true),(25,true),(552,false)]
theorem inputList14180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14180 = (containClause5 13 25) := by decide
  rw [he]
  exact input_contain 13 25 (by decide) v hb
mask_input "14180|14742040721959145907193572581985425355144223517251720423344555860334469384344331453461432520225229560708860839963921269139728846210643721220943102544658968920505450496|33562624"
def inputClause14185 : CNF.NClause := [(13,true),(30,true),(557,false)]
theorem inputList14185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14185 = (containClause5 13 30) := by decide
  rw [he]
  exact input_contain 13 30 (by decide) v hb
mask_input "14185|471745303102692669030194322623533611364615152552055053547025787530703020299018606510765840647207345942683546878845480612471323078740599079070179281429087005456174415872|1073750016"
def inputClause14186 : CNF.NClause := [(14,true),(0,true),(558,false)]
theorem inputList14186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14186 = (containClause5 14 0) := by decide
  rw [he]
  exact input_contain 14 0 (by decide) v hb
mask_input "14186|943490606205385338060388645247067222729230305104110107094051575061406040598037213021531681294414691885367093757690961224942646157481198158140358562858174010912348831744|16385"
def inputClause14210 : CNF.NClause := [(14,true),(25,true),(583,false)]
theorem inputList14210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14210 = (containClause5 14 25) := by decide
  rw [he]
  exact input_contain 14 25 (by decide) v hb
mask_input "14210|31658291388557380359744322690514840324496812684955115509000071179890844813636078997800499335839109758668501942530065835436974724391264154875845907853042325493325666835033489408|33570816"
def inputClause14215 : CNF.NClause := [(14,true),(30,true),(588,false)]
theorem inputList14215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14215 = (containClause5 14 30) := by decide
  rw [he]
  exact input_contain 14 30 (by decide) v hb
mask_input "14215|1013065324433836171511818326096474890383898005918563696288002277756507034036354527929615978746851512277392062160962106733983191180520452956027069051297354415786421338721071661056|1073758208"
def inputClause14216 : CNF.NClause := [(15,true),(0,true),(589,false)]
theorem inputList14216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14216 = (containClause5 15 0) := by decide
  rw [he]
  exact input_contain 15 0 (by decide) v hb
mask_input "14216|2026130648867672343023636652192949780767796011837127392576004555513014068072709055859231957493703024554784124321924213467966382361040905912054138102594708831572842677442143322112|32769"
def inputClause14240 : CNF.NClause := [(15,true),(25,true),(614,false)]
theorem inputList14240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14240 = (containClause5 15 25) := by decide
  rw [he]
  exact input_contain 15 25 (by decide) v hb
mask_input "14240|67985663080546188632267290438715984298187919069060086169528849689651655662189087070612800289949348565617834174239552129964362155219546526644418557282123181048810402666930332036061200384|33587200"
def inputClause14245 : CNF.NClause := [(15,true),(30,true),(619,false)]
theorem inputList14245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14245 = (containClause5 15 30) := by decide
  rw [he]
  exact input_contain 15 30 (by decide) v hb
mask_input "14245|2175541218577478036232553294038911497542013410209922757424923190068852981190050786259609609278379154099770693575665668158859588967025488852621393833027941793561932885341770625153958412288|1073774592"
def inputClause14246 : CNF.NClause := [(16,true),(0,true),(620,false)]
theorem inputList14246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14246 = (containClause5 16 0) := by decide
  rw [he]
  exact input_contain 16 0 (by decide) v hb
mask_input "14246|4351082437154956072465106588077822995084026820419845514849846380137705962380101572519219218556758308199541387151331336317719177934050977705242787666055883587123865770683541250307916824576|65537"
def inputClause14270 : CNF.NClause := [(16,true),(25,true),(645,false)]
theorem inputList14270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14270 = (containClause5 16 25) := by decide
  rw [he]
  exact input_contain 16 25 (by decide) v hb
mask_input "14270|145998099763910246996517491382409322396583312231953917778534160572776805350677676368189209962155884792916553906355021033942038551084014015944085162231110854024063829579528478402651974151891320832|33619968"
def inputClause14275 : CNF.NClause := [(16,true),(30,true),(650,false)]
theorem inputList14275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14275 = (containClause5 16 30) := by decide
  rw [he]
  exact input_contain 16 30 (by decide) v hb
mask_input "14275|4671939192445127903888559724237098316690665991422525368913093138328857771221685643782054718788988313373329725003360673086145233634688448510210725191395547328770042546544911308884863172860522266624|1073807360"
def inputClause14276 : CNF.NClause := [(17,true),(0,true),(651,false)]
theorem inputList14276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14276 = (containClause5 17 0) := by decide
  rw [he]
  exact input_contain 17 0 (by decide) v hb
mask_input "14276|9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345721044533248|131073"
def inputClause14300 : CNF.NClause := [(17,true),(25,true),(676,false)]
theorem inputList14300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14300 = (containClause5 17 25) := by decide
  rw [he]
  exact input_contain 17 25 (by decide) v hb
mask_input "14300|313528531882069915964662425689704934689422834087799421518938595239444503444259215719322355763768461419760165742407930953086580768238532773442734168210737755891992072530296122920016274326105279759841755136|33685504"
def inputClause14305 : CNF.NClause := [(17,true),(30,true),(681,false)]
theorem inputList14305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14305
  have he : decodeClause inputClause14305 = containClause5 17 30 := by decide
  rw [he]
  exact input_contain 17 30 (by decide) v hb
mask_input "14305|10032913020226237310869197622070557910061530690809581488606035047662224110216294903018315384440590765432325303757053790498770584583633048750167493382743608188543746320969475933440520778435368952314936164352|1073872896"
def inputClause14306 : CNF.NClause := [(18,true),(0,true),(682,false)]
theorem inputList14306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14306 = (containClause5 18 0) := by decide
  rw [he]
  exact input_contain 18 0 (by decide) v hb
mask_input "14306|20065826040452474621738395244141115820123061381619162977212070095324448220432589806036630768881181530864650607514107580997541169167266097500334986765487216377087492641938951866881041556870737904629872328704|262145"
def inputClause14330 : CNF.NClause := [(18,true),(25,true),(707,false)]
theorem inputList14330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14330 = (containClause5 18 25) := by decide
  rw [he]
  exact input_contain 18 25 (by decide) v hb
mask_input "14330|673297395398191808926846705008656469190443494761366254015779955592797715750026345230549316643531321757053820013590811867266487328023526894480360290643440748794268629904440908568532961009193307810725536222180016128|33816576"
def inputClause14335 : CNF.NClause := [(18,true),(30,true),(712,false)]
theorem inputList14335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14335 = (containClause5 18 30) := by decide
  rw [he]
  exact input_contain 18 30 (by decide) v hb
mask_input "14335|21545516652742137885659094560277007014094191832363720128504958578969526904000843047377578132593002296225722240434905979752527594496752860623371529300590103961416596156942109074193054752294185849943217159109760516096|1074003968"
def inputClause14336 : CNF.NClause := [(19,true),(0,true),(713,false)]
theorem inputList14336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14336 = (containClause5 19 0) := by decide
  rw [he]
  exact input_contain 19 0 (by decide) v hb
mask_input "14336|43091033305484275771318189120554014028188383664727440257009917157939053808001686094755156265186004592451444480869811959505055188993505721246743058601180207922833192313884218148386109504588371699886434318219521032192|524289"
def inputClause14360 : CNF.NClause := [(19,true),(25,true),(738,false)]
theorem inputList14360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14360 = (containClause5 19 25) := by decide
  rw [he]
  exact input_contain 19 25 (by decide) v hb
mask_input "14360|1445895146858607358437943727208769466035893202868007692637901788601699241144933631951807447549557758449099707135121406247999127995329736165184795181305316406492567598839150653733187621116264206194563768053163279547256274944|34078720"
def inputClause14365 : CNF.NClause := [(19,true),(30,true),(743,false)]
theorem inputList14365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14365 = (containClause5 19 30) := by decide
  rw [he]
  exact input_contain 19 30 (by decide) v hb
mask_input "14365|46268644699475435470014199270680622913148582491776246164412857235254375716637876222457838321585848270371190628323884999935972095850551557285913445801770125007762163162852820919462003875720454598226040577701224945512200798208|1074266112"
def inputClause14366 : CNF.NClause := [(20,true),(0,true),(744,false)]
theorem inputList14366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14366 = (containClause5 20 0) := by decide
  rw [he]
  exact input_contain 20 0 (by decide) v hb
mask_input "14366|92537289398950870940028398541361245826297164983552492328825714470508751433275752444915676643171696540742381256647769999871944191701103114571826891603540250015524326325705641838924007751440909196452081155402449891024401596416|1048577"
def inputClause14390 : CNF.NClause := [(20,true),(25,true),(769,false)]
theorem inputList14390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14390 = (containClause5 20 25) := by decide
  rw [he]
  exact input_contain 20 25 (by decide) v hb
mask_input "14390|3105036184601417870297958976925005110513772034233393222278104076052101905372753772661756817657292955900975461394262146412343160088229628782888574550082362278408909952041699811100530571263196889650525998387432937501785693707632115712|34603008"
end Percolation.MaskChain
