import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14174 : CNF.NClause := [(13,true),(19,true),(546,false)]
theorem inputList14174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14174 = (containClause5 13 19) := by decide
  rw [he]
  exact input_contain 13 19 (by decide) v hb
mask_input "14174|230344386280611654799899571593522271174128492457058131614758685317726084130380178960334883128519211886075950624436269830308263222041308144077235977260296389382897664|532480"
def inputClause14175 : CNF.NClause := [(13,true),(20,true),(547,false)]
theorem inputList14175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14175 = (containClause5 13 20) := by decide
  rw [he]
  exact input_contain 13 20 (by decide) v hb
mask_input "14175|460688772561223309599799143187044542348256984914116263229517370635452168260760357920669766257038423772151901248872539660616526444082616288154471954520592778765795328|1056768"
def inputClause14176 : CNF.NClause := [(13,true),(21,true),(548,false)]
theorem inputList14176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14176 = (containClause5 13 21) := by decide
  rw [he]
  exact input_contain 13 21 (by decide) v hb
mask_input "14176|921377545122446619199598286374089084696513969828232526459034741270904336521520715841339532514076847544303802497745079321233052888165232576308943909041185557531590656|2105344"
def inputClause14177 : CNF.NClause := [(13,true),(22,true),(549,false)]
theorem inputList14177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14177 = (containClause5 13 22) := by decide
  rw [he]
  exact input_contain 13 22 (by decide) v hb
mask_input "14177|1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312|4202496"
def inputClause14178 : CNF.NClause := [(13,true),(23,true),(550,false)]
theorem inputList14178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14178 = (containClause5 13 23) := by decide
  rw [he]
  exact input_contain 13 23 (by decide) v hb
mask_input "14178|3685510180489786476798393145496356338786055879312930105836138965083617346086082863365358130056307390177215209990980317284932211552660930305235775636164742230126362624|8396800"
def inputClause14179 : CNF.NClause := [(13,true),(24,true),(551,false)]
theorem inputList14179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14179 = (containClause5 13 24) := by decide
  rw [he]
  exact input_contain 13 24 (by decide) v hb
mask_input "14179|7371020360979572953596786290992712677572111758625860211672277930167234692172165726730716260112614780354430419981960634569864423105321860610471551272329484460252725248|16785408"
def inputClause14181 : CNF.NClause := [(13,true),(26,true),(553,false)]
theorem inputList14181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14181 = (containClause5 13 26) := by decide
  rw [he]
  exact input_contain 13 26 (by decide) v hb
mask_input "14181|29484081443918291814387145163970850710288447034503440846689111720668938768688662906922865040450459121417721679927842538279457692421287442441886205089317937841010900992|67117056"
def inputClause14182 : CNF.NClause := [(13,true),(27,true),(554,false)]
theorem inputList14182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14182 = (containClause5 13 27) := by decide
  rw [he]
  exact input_contain 13 27 (by decide) v hb
mask_input "14182|58968162887836583628774290327941701420576894069006881693378223441337877537377325813845730080900918242835443359855685076558915384842574884883772410178635875682021801984|134225920"
def inputClause14183 : CNF.NClause := [(13,true),(28,true),(555,false)]
theorem inputList14183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14183 = (containClause5 13 28) := by decide
  rw [he]
  exact input_contain 13 28 (by decide) v hb
mask_input "14183|117936325775673167257548580655883402841153788138013763386756446882675755074754651627691460161801836485670886719711370153117830769685149769767544820357271751364043603968|268443648"
def inputClause14184 : CNF.NClause := [(13,true),(29,true),(556,false)]
theorem inputList14184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14184 = (containClause5 13 29) := by decide
  rw [he]
  exact input_contain 13 29 (by decide) v hb
mask_input "14184|235872651551346334515097161311766805682307576276027526773512893765351510149509303255382920323603672971341773439422740306235661539370299539535089640714543502728087207936|536879104"
def inputClause14189 : CNF.NClause := [(14,true),(3,true),(561,false)]
theorem inputList14189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14189 = (containClause5 14 3) := by decide
  rw [he]
  exact input_contain 14 3 (by decide) v hb
mask_input "14189|7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087298790653952|16392"
def inputClause14192 : CNF.NClause := [(14,true),(6,true),(564,false)]
theorem inputList14192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14192 = (containClause5 14 6) := by decide
  rw [he]
  exact input_contain 14 6 (by decide) v hb
mask_input "14192|60383398797144661635864873295812302254670739526663046854019300803929986598274381633378027602842540280663494000492221518396329354078796682120982948022923136698390325231616|16448"
def inputClause14198 : CNF.NClause := [(14,true),(12,true),(570,false)]
theorem inputList14198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14198 = (containClause5 14 12) := by decide
  rw [he]
  exact input_contain 14 12 (by decide) v hb
mask_input "14198|3864537523017258344695351890931987344298927329706434998657235251451519142289560424536193766581922577962463616031502177177365078661042987655742908673467080748696980814823424|20480"
def inputClause14199 : CNF.NClause := [(14,true),(13,true),(571,false)]
theorem inputList14199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14199 = (containClause5 14 13) := by decide
  rw [he]
  exact input_contain 14 13 (by decide) v hb
mask_input "14199|7729075046034516689390703781863974688597854659412869997314470502903038284579120849072387533163845155924927232063004354354730157322085975311485817346934161497393961629646848|24576"
def inputClause14200 : CNF.NClause := [(14,true),(15,true),(573,false)]
theorem inputList14200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14200 = (containClause5 14 15) := by decide
  rw [he]
  exact input_contain 14 15 (by decide) v hb
mask_input "14200|30916300184138066757562815127455898754391418637651479989257882011612153138316483396289550132655380623699708928252017417418920629288343901245943269387736645989575846518587392|49152"
def inputClause14201 : CNF.NClause := [(14,true),(16,true),(574,false)]
theorem inputList14201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14201 = (containClause5 14 16) := by decide
  rw [he]
  exact input_contain 14 16 (by decide) v hb
mask_input "14201|61832600368276133515125630254911797508782837275302959978515764023224306276632966792579100265310761247399417856504034834837841258576687802491886538775473291979151693037174784|81920"
def inputClause14202 : CNF.NClause := [(14,true),(17,true),(575,false)]
theorem inputList14202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14202 = (containClause5 14 17) := by decide
  rw [he]
  exact input_contain 14 17 (by decide) v hb
mask_input "14202|123665200736552267030251260509823595017565674550605919957031528046448612553265933585158200530621522494798835713008069669675682517153375604983773077550946583958303386074349568|147456"
def inputClause14203 : CNF.NClause := [(14,true),(18,true),(576,false)]
theorem inputList14203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14203 = (containClause5 14 18) := by decide
  rw [he]
  exact input_contain 14 18 (by decide) v hb
mask_input "14203|247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136|278528"
def inputClause14204 : CNF.NClause := [(14,true),(19,true),(577,false)]
theorem inputList14204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14204 = (containClause5 14 19) := by decide
  rw [he]
  exact input_contain 14 19 (by decide) v hb
mask_input "14204|494660802946209068121005042039294380070262698202423679828126112185794450213063734340632802122486089979195342852032278678702730068613502419935092310203786335833213544297398272|540672"
def inputClause14205 : CNF.NClause := [(14,true),(20,true),(578,false)]
theorem inputList14205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14205 = (containClause5 14 20) := by decide
  rw [he]
  exact input_contain 14 20 (by decide) v hb
mask_input "14205|989321605892418136242010084078588760140525396404847359656252224371588900426127468681265604244972179958390685704064557357405460137227004839870184620407572671666427088594796544|1064960"
def inputClause14206 : CNF.NClause := [(14,true),(21,true),(579,false)]
theorem inputList14206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14206 = (containClause5 14 21) := by decide
  rw [he]
  exact input_contain 14 21 (by decide) v hb
mask_input "14206|1978643211784836272484020168157177520281050792809694719312504448743177800852254937362531208489944359916781371408129114714810920274454009679740369240815145343332854177189593088|2113536"
def inputClause14207 : CNF.NClause := [(14,true),(22,true),(580,false)]
theorem inputList14207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14207 = (containClause5 14 22) := by decide
  rw [he]
  exact input_contain 14 22 (by decide) v hb
mask_input "14207|3957286423569672544968040336314355040562101585619389438625008897486355601704509874725062416979888719833562742816258229429621840548908019359480738481630290686665708354379186176|4210688"
def inputClause14208 : CNF.NClause := [(14,true),(23,true),(581,false)]
theorem inputList14208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14208 = (containClause5 14 23) := by decide
  rw [he]
  exact input_contain 14 23 (by decide) v hb
mask_input "14208|7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416708758372352|8404992"
def inputClause14209 : CNF.NClause := [(14,true),(24,true),(582,false)]
theorem inputList14209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14209 = (containClause5 14 24) := by decide
  rw [he]
  exact input_contain 14 24 (by decide) v hb
mask_input "14209|15829145694278690179872161345257420162248406342477557754500035589945422406818039498900249667919554879334250971265032917718487362195632077437922953926521162746662833417516744704|16793600"
def inputClause14211 : CNF.NClause := [(14,true),(26,true),(584,false)]
theorem inputList14211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14211 = (containClause5 14 26) := by decide
  rw [he]
  exact input_contain 14 26 (by decide) v hb
mask_input "14211|63316582777114760719488645381029680648993625369910231018000142359781689627272157995600998671678219517337003885060131670873949448782528309751691815706084650986651333670066978816|67125248"
def inputClause14212 : CNF.NClause := [(14,true),(27,true),(585,false)]
theorem inputList14212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14212 = (containClause5 14 27) := by decide
  rw [he]
  exact input_contain 14 27 (by decide) v hb
mask_input "14212|126633165554229521438977290762059361297987250739820462036000284719563379254544315991201997343356439034674007770120263341747898897565056619503383631412169301973302667340133957632|134234112"
def inputClause14213 : CNF.NClause := [(14,true),(28,true),(586,false)]
theorem inputList14213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14213 = (containClause5 14 28) := by decide
  rw [he]
  exact input_contain 14 28 (by decide) v hb
mask_input "14213|253266331108459042877954581524118722595974501479640924072000569439126758509088631982403994686712878069348015540240526683495797795130113239006767262824338603946605334680267915264|268451840"
def inputClause14214 : CNF.NClause := [(14,true),(29,true),(587,false)]
theorem inputList14214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14214 = (containClause5 14 29) := by decide
  rw [he]
  exact input_contain 14 29 (by decide) v hb
mask_input "14214|506532662216918085755909163048237445191949002959281848144001138878253517018177263964807989373425756138696031080481053366991595590260226478013534525648677207893210669360535830528|536887296"
def inputClause14219 : CNF.NClause := [(15,true),(3,true),(592,false)]
theorem inputList14219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14219 = (containClause5 15 3) := by decide
  rw [he]
  exact input_contain 15 3 (by decide) v hb
mask_input "14219|16209045190941378744189093217543598246142368094697019140608036444104112544581672446873855659949624196438272994575393707743731058888327247296433104820757670652582741419537146576896|32776"
def inputClause14222 : CNF.NClause := [(15,true),(6,true),(595,false)]
theorem inputList14222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14222 = (containClause5 15 6) := by decide
  rw [he]
  exact input_contain 15 6 (by decide) v hb
mask_input "14222|129672361527531029953512745740348785969138944757576153124864291552832900356653379574990845279596993571506183956603149661949848471106617978371464838566061365220661931356297172615168|32832"
def inputClause14223 : CNF.NClause := [(15,true),(7,true),(596,false)]
theorem inputList14223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14223 = (containClause5 15 7) := by decide
  rw [he]
  exact input_contain 15 7 (by decide) v hb
mask_input "14223|259344723055062059907025491480697571938277889515152306249728583105665800713306759149981690559193987143012367913206299323899696942213235956742929677132122730441323862712594345230336|32896"
def inputClause14225 : CNF.NClause := [(15,true),(9,true),(598,false)]
theorem inputList14225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14225 = (containClause5 15 9) := by decide
  rw [he]
  exact input_contain 15 9 (by decide) v hb
mask_input "14225|1037378892220248239628101965922790287753111558060609224998914332422663202853227036599926762236775948572049471652825197295598787768852943826971718708528490921765295450850377380921344|33280"
def inputClause14228 : CNF.NClause := [(15,true),(12,true),(601,false)]
theorem inputList14228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14228 = (containClause5 15 12) := by decide
  rw [he]
  exact input_contain 15 12 (by decide) v hb
mask_input "14228|8299031137761985917024815727382322302024892464484873799991314659381305622825816292799414097894207588576395773222601578364790302150823550615773749668227927374122363606803019047370752|36864"
def inputClause14229 : CNF.NClause := [(15,true),(13,true),(602,false)]
theorem inputList14229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14229 = (containClause5 15 13) := by decide
  rw [he]
  exact input_contain 15 13 (by decide) v hb
mask_input "14229|16598062275523971834049631454764644604049784928969747599982629318762611245651632585598828195788415177152791546445203156729580604301647101231547499336455854748244727213606038094741504|40960"
def inputClause14230 : CNF.NClause := [(15,true),(14,true),(603,false)]
theorem inputList14230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14230 = (containClause5 15 14) := by decide
  rw [he]
  exact input_contain 15 14 (by decide) v hb
mask_input "14230|33196124551047943668099262909529289208099569857939495199965258637525222491303265171197656391576830354305583092890406313459161208603294202463094998672911709496489454427212076189483008|49152"
def inputClause14231 : CNF.NClause := [(15,true),(16,true),(605,false)]
theorem inputList14231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14231 = (containClause5 15 16) := by decide
  rw [he]
  exact input_contain 15 16 (by decide) v hb
mask_input "14231|132784498204191774672397051638117156832398279431757980799861034550100889965213060684790625566307321417222332371561625253836644834413176809852379994691646837985957817708848304757932032|98304"
def inputClause14232 : CNF.NClause := [(15,true),(17,true),(606,false)]
theorem inputList14232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14232 = (containClause5 15 17) := by decide
  rw [he]
  exact input_contain 15 17 (by decide) v hb
mask_input "14232|265568996408383549344794103276234313664796558863515961599722069100201779930426121369581251132614642834444664743123250507673289668826353619704759989383293675971915635417696609515864064|163840"
def inputClause14233 : CNF.NClause := [(15,true),(18,true),(607,false)]
theorem inputList14233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14233 = (containClause5 15 18) := by decide
  rw [he]
  exact input_contain 15 18 (by decide) v hb
mask_input "14233|531137992816767098689588206552468627329593117727031923199444138200403559860852242739162502265229285668889329486246501015346579337652707239409519978766587351943831270835393219031728128|294912"
def inputClause14234 : CNF.NClause := [(15,true),(19,true),(608,false)]
theorem inputList14234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14234 = (containClause5 15 19) := by decide
  rw [he]
  exact input_contain 15 19 (by decide) v hb
mask_input "14234|1062275985633534197379176413104937254659186235454063846398888276400807119721704485478325004530458571337778658972493002030693158675305414478819039957533174703887662541670786438063456256|557056"
def inputClause14235 : CNF.NClause := [(15,true),(20,true),(609,false)]
theorem inputList14235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14235 = (containClause5 15 20) := by decide
  rw [he]
  exact input_contain 15 20 (by decide) v hb
mask_input "14235|2124551971267068394758352826209874509318372470908127692797776552801614239443408970956650009060917142675557317944986004061386317350610828957638079915066349407775325083341572876126912512|1081344"
end Percolation.MaskChain
