import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14346 : CNF.NClause := [(19,true),(10,true),(723,false)]
theorem inputList14346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14346 = (containClause5 19 10) := by decide
  rw [he]
  exact input_contain 19 10 (by decide) v hb
mask_input "14346|44125218104815898389829825659447310364864904872680898823178155169729591099393726561029280015550468702670279148410687446533176513529349858556664892007608532912981188929417439383947376132698492620683708741856789536964608|525312"
def inputClause14347 : CNF.NClause := [(19,true),(11,true),(724,false)]
theorem inputList14347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14347 = (containClause5 19 11) := by decide
  rw [he]
  exact input_contain 19 11 (by decide) v hb
mask_input "14347|88250436209631796779659651318894620729729809745361797646356310339459182198787453122058560031100937405340558296821374893066353027058699717113329784015217065825962377858834878767894752265396985241367417483713579073929216|526336"
def inputClause14350 : CNF.NClause := [(19,true),(14,true),(727,false)]
theorem inputList14350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14350
  have he : decodeClause inputClause14350 = containClause5 19 14 := by decide
  rw [he]
  exact input_contain 19 14 (by decide) v hb
mask_input "14350|706003489677054374237277210551156965837838477962894381170850482715673457590299624976468480248807499242724466374570999144530824216469597736906638272121736526607699022870679030143158018123175881930939339869708632591433728|540672"
def inputClause14397 : CNF.NClause := [(21,true),(1,true),(776,false)]
theorem inputList14397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14397
  have he : decodeClause inputClause14397 = containClause5 21 1 := by decide
  rw [he]
  exact input_contain 21 1 (by decide) v hb
mask_input "14397|397444631628981487398138749046400654145762820381874332451597321734669043887712482900704872660133498355324859058465554740779924491293392484209737542410542371636340473861337575820867913121689201875267327793591416000228568794576910811136|2097154"
def inputClause14398 : CNF.NClause := [(21,true),(2,true),(777,false)]
theorem inputList14398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14398
  have he : decodeClause inputClause14398 = containClause5 21 2 := by decide
  rw [he]
  exact input_contain 21 2 (by decide) v hb
mask_input "14398|794889263257962974796277498092801308291525640763748664903194643469338087775424965801409745320266996710649718116931109481559848982586784968419475084821084743272680947722675151641735826243378403750534655587182832000457137589153821622272|2097156"
def inputClause14401 : CNF.NClause := [(21,true),(5,true),(780,false)]
theorem inputList14401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14401
  have he : decodeClause inputClause14401 = containClause5 21 5 := by decide
  rw [he]
  exact input_contain 21 5 (by decide) v hb
mask_input "14401|6359114106063703798370219984742410466332205126109989319225557147754704702203399726411277962562135973685197744935448875852478791860694279747355800678568677946181447581781401213133886609947027230004277244697462656003657100713230572978176|2097184"
def inputClause14404 : CNF.NClause := [(21,true),(8,true),(783,false)]
theorem inputList14404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14404 = (containClause5 21 8) := by decide
  rw [he]
  exact input_contain 21 8 (by decide) v hb
mask_input "14404|50872912848509630386961759877939283730657641008879914553804457182037637617627197811290223700497087789481581959483591006819830334885554237978846405428549423569451580654251209705071092879576217840034217957579701248029256805705844583825408|2097408"
def inputClause14406 : CNF.NClause := [(21,true),(10,true),(785,false)]
theorem inputList14406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14406
  have he : decodeClause inputClause14406 = containClause5 21 10 := by decide
  rw [he]
  exact input_contain 21 10 (by decide) v hb
mask_input "14406|203491651394038521547847039511757134922630564035519658215217828728150550470508791245160894801988351157926327837934364027279321339542216951915385621714197694277806322617004838820284371518304871360136871830318804992117027222823378335301632|2098176"
def inputClause14407 : CNF.NClause := [(21,true),(11,true),(786,false)]
theorem inputList14407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14407
  have he : decodeClause inputClause14407 = containClause5 21 11 := by decide
  rw [he]
  exact input_contain 21 11 (by decide) v hb
mask_input "14407|406983302788077043095694079023514269845261128071039316430435657456301100941017582490321789603976702315852655675868728054558642679084433903830771243428395388555612645234009677640568743036609742720273743660637609984234054445646756670603264|2099200"
def inputClause14427 : CNF.NClause := [(22,true),(1,true),(807,false)]
theorem inputList14427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14427 = (containClause5 22 1) := by decide
  rw [he]
  exact input_contain 22 1 (by decide) v hb
mask_input "14427|853505847408621347082221029212320998034529065256436244530720999905796766440656905154743321711558949215095028555959454777073766611727278730286509574698346245900180170177793863483274020596712195165307522065393485053656415748796987045268976304128|4194306"
def inputClause14428 : CNF.NClause := [(22,true),(2,true),(808,false)]
theorem inputList14428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14428
  have he : decodeClause inputClause14428 = containClause5 22 2 := by decide
  rw [he]
  exact input_contain 22 2 (by decide) v hb
mask_input "14428|1707011694817242694164442058424641996069058130512872489061441999811593532881313810309486643423117898430190057111918909554147533223454557460573019149396692491800360340355587726966548041193424390330615044130786970107312831497593974090537952608256|4194308"
def inputClause14431 : CNF.NClause := [(22,true),(5,true),(811,false)]
theorem inputList14431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14431 = (containClause5 22 5) := by decide
  rw [he]
  exact input_contain 22 5 (by decide) v hb
mask_input "14431|13656093558537941553315536467397135968552465044102979912491535998492748263050510482475893147384943187441520456895351276433180265787636459684584153195173539934402882722844701815732384329547395122644920353046295760858502651980751792724303620866048|4194336"
def inputClause14434 : CNF.NClause := [(22,true),(8,true),(814,false)]
theorem inputList14434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14434 = (containClause5 22 8) := by decide
  rw [he]
  exact input_contain 22 8 (by decide) v hb
mask_input "14434|109248748468303532426524291739177087748419720352823839299932287987941986104404083859807145179079545499532163655162810211465442126301091677476673225561388319475223061782757614525859074636379160981159362824370366086868021215846014341794428966928384|4194560"
def inputClause14436 : CNF.NClause := [(22,true),(10,true),(816,false)]
theorem inputList14436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14436
  have he : decodeClause inputClause14436 = containClause5 22 10 := by decide
  rw [he]
  exact input_contain 22 10 (by decide) v hb
mask_input "14436|436994993873214129706097166956708350993678881411295357199729151951767944417616335439228580716318181998128654620651240845861768505204366709906692902245553277900892247131030458103436298545516643924637451297481464347472084863384057367177715867713536|4195328"
def inputClause14437 : CNF.NClause := [(22,true),(11,true),(817,false)]
theorem inputList14437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14437 = (containClause5 22 11) := by decide
  rw [he]
  exact input_contain 22 11 (by decide) v hb
mask_input "14437|873989987746428259412194333913416701987357762822590714399458303903535888835232670878457161432636363996257309241302481691723537010408733419813385804491106555801784494262060916206872597091033287849274902594962928694944169726768114734355431735427072|4196352"
def inputClause14487 : CNF.NClause := [(24,true),(1,true),(869,false)]
theorem inputList14487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14487 = (containClause5 24 1) := by decide
  rw [he]
  exact input_contain 24 1 (by decide) v hb
mask_input "14487|3936100983140358674171118325863157261303419813782882110237782515784158576702511753696331798193284779002326689610310857585686054524054270515222392815820422596546908348791339130466666204306680269934417552562141332061201544797059608540225005885713074181150932467712|16777218"
def inputClause14488 : CNF.NClause := [(24,true),(2,true),(870,false)]
theorem inputList14488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14488 = (containClause5 24 2) := by decide
  rw [he]
  exact input_contain 24 2 (by decide) v hb
mask_input "14488|7872201966280717348342236651726314522606839627565764220475565031568317153405023507392663596386569558004653379220621715171372109048108541030444785631640845193093816697582678260933332408613360539868835105124282664122403089594119217080450011771426148362301864935424|16777220"
def inputClause14491 : CNF.NClause := [(24,true),(5,true),(873,false)]
theorem inputList14491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14491 = (containClause5 24 5) := by decide
  rw [he]
  exact input_contain 24 5 (by decide) v hb
mask_input "14491|62977615730245738786737893213810516180854717020526113763804520252546537227240188059141308771092556464037227033764973721370976872384868328243558285053126761544750533580661426087466659268906884318950680840994261312979224716752953736643600094171409186898414919483392|16777248"
def inputClause14494 : CNF.NClause := [(24,true),(8,true),(876,false)]
theorem inputList14494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14494 = (containClause5 24 8) := by decide
  rw [he]
  exact input_contain 24 8 (by decide) v hb
mask_input "14494|503820925841965910293903145710484129446837736164208910110436162020372297817921504473130470168740451712297816270119789770967814979078946625948466280425014092358004268645291408699733274151255074551605446727954090503833797734023629893148800753371273495187319355867136|16777472"
def inputClause14496 : CNF.NClause := [(24,true),(10,true),(878,false)]
theorem inputList14496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14496 = (containClause5 24 10) := by decide
  rw [he]
  exact input_contain 24 10 (by decide) v hb
mask_input "14496|2015283703367863641175612582841936517787350944656835640441744648081489191271686017892521880674961806849191265080479159083871259916315786503793865121700056369432017074581165634798933096605020298206421786911816362015335190936094519572595203013485093980749277423468544|16778240"
def inputClause14497 : CNF.NClause := [(24,true),(11,true),(879,false)]
theorem inputList14497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14497 = (containClause5 24 11) := by decide
  rw [he]
  exact input_contain 24 11 (by decide) v hb
mask_input "14497|4030567406735727282351225165683873035574701889313671280883489296162978382543372035785043761349923613698382530160958318167742519832631573007587730243400112738864034149162331269597866193210040596412843573823632724030670381872189039145190406026970187961498554846937088|16779264"
def inputClause14547 : CNF.NClause := [(26,true),(1,true),(931,false)]
theorem inputList14547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14547 = (containClause5 26 1) := by decide
  rw [he]
  exact input_contain 26 1 (by decide) v hb
mask_input "14547|18152061871066687778296661354368903321914797383537530017770652579540291225102592450502542901564408576535628952517004065557306948798155587253306037366972590646764780767180906664339433713797579795779287057890032192456881698082005372169886461674177955114893128728688280185836979355648|67108866"
def inputClause14548 : CNF.NClause := [(26,true),(2,true),(932,false)]
theorem inputList14548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14548 = (containClause5 26 2) := by decide
  rw [he]
  exact input_contain 26 2 (by decide) v hb
mask_input "14548|36304123742133375556593322708737806643829594767075060035541305159080582450205184901005085803128817153071257905034008131114613897596311174506612074733945181293529561534361813328678867427595159591558574115780064384913763396164010744339772923348355910229786257457376560371673958711296|67108868"
def inputClause14551 : CNF.NClause := [(26,true),(5,true),(935,false)]
theorem inputList14551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14551 = (containClause5 26 5) := by decide
  rw [he]
  exact input_contain 26 5 (by decide) v hb
mask_input "14551|290432989937067004452746581669902453150636758136600480284330441272644659601641479208040686425030537224570063240272065048916911180770489396052896597871561450348236492274894506629430939420761276732468592926240515079310107169312085954718183386786847281838290059659012482973391669690368|67108896"
def inputClause14554 : CNF.NClause := [(26,true),(8,true),(938,false)]
theorem inputList14554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14554 = (containClause5 26 8) := by decide
  rw [he]
  exact input_contain 26 8 (by decide) v hb
mask_input "14554|2323463919496536035621972653359219625205094065092803842274643530181157276813131833664325491400244297796560505922176520391335289446163915168423172782972491602785891938199156053035447515366090213859748743409924120634480857354496687637745467094294778254706320477272099863787133357522944|67109120"
def inputClause14555 : CNF.NClause := [(26,true),(9,true),(939,false)]
theorem inputList14555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14555 = (containClause5 26 9) := by decide
  rw [he]
  exact input_contain 26 9 (by decide) v hb
mask_input "14555|4646927838993072071243945306718439250410188130185607684549287060362314553626263667328650982800488595593121011844353040782670578892327830336846345565944983205571783876398312106070895030732180427719497486819848241268961714708993375275490934188589556509412640954544199727574266715045888|67109376"
def inputClause14556 : CNF.NClause := [(26,true),(10,true),(940,false)]
theorem inputList14556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14556 = (containClause5 26 10) := by decide
  rw [he]
  exact input_contain 26 10 (by decide) v hb
mask_input "14556|9293855677986144142487890613436878500820376260371215369098574120724629107252527334657301965600977191186242023688706081565341157784655660673692691131889966411143567752796624212141790061464360855438994973639696482537923429417986750550981868377179113018825281909088399455148533430091776|67109888"
def inputClause14557 : CNF.NClause := [(26,true),(11,true),(941,false)]
theorem inputList14557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14557 = (containClause5 26 11) := by decide
  rw [he]
  exact input_contain 26 11 (by decide) v hb
mask_input "14557|18587711355972288284975781226873757001640752520742430738197148241449258214505054669314603931201954382372484047377412163130682315569311321347385382263779932822287135505593248424283580122928721710877989947279392965075846858835973501101963736754358226037650563818176798910297066860183552|67110912"
def inputClause14560 : CNF.NClause := [(26,true),(14,true),(944,false)]
theorem inputList14560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14560 = (containClause5 26 14) := by decide
  rw [he]
  exact input_contain 26 14 (by decide) v hb
mask_input "14560|148701690847778306279806249814990056013126020165939445905577185931594065716040437354516831449615635058979872379019297305045458524554490570779083058110239462578297084044745987394268640983429773687023919578235143720606774870687788008815709894034865808301204510545414391282376534881468416|67125248"
def inputClause14607 : CNF.NClause := [(28,true),(1,true),(993,false)]
theorem inputList14607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14607 = (containClause5 28 1) := by decide
  rw [he]
  exact input_contain 28 1 (by decide) v hb
mask_input "14607|83711609936427134449095706957812641450109750914494813081542999091433675869135634569781123344976238916218333821683839595717745725444712034656129512302332615655738810740814304573602145352049774545921517048070675585809233916151552871555980812078727054020087472481926110684847108059786128022165669281792|268435458"
def inputClause14616 : CNF.NClause := [(28,true),(10,true),(1002,false)]
theorem inputList14616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14616
  have he : decodeClause inputClause14616 = containClause5 28 10 := by decide
  rw [he]
  exact input_contain 28 10 (by decide) v hb
mask_input "14616|42860344287450692837937001962400072422456192468221344297750015534814042044997444899727935152627834325103786916702125873007485811427692561743938310298794299215738271099296923941684298420249484567511816728612185899934327765069595070236662175784308251658284785910746168670641719326610497547348822672277504|268436480"
def inputClause14626 : CNF.NClause := [(28,true),(20,true),(1012,false)]
theorem inputList14626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14626
  have he : decodeClause inputClause14626 = containClause5 28 20 := by decide
  rw [he]
  exact input_contain 28 20 (by decide) v hb
mask_input "14626|43888992550349509466047490009497674160595141087458656560896015907649579054077383577321405596290902348906277802702976893959665470901957183225792829745965362396915989605680050116284721582335472197132100330098878361532751631431265351922342068003131649698083620772604076718737120590449149488485194416412164096|269484032"
def inputClause14632 : CNF.NClause := [(28,true),(26,true),(1018,false)]
theorem inputList14632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14632 = (containClause5 28 26) := by decide
  rw [he]
  exact input_contain 28 26 (by decide) v hb
mask_input "14632|2808895523222368605827039360607851146278089029597354019897345018089573059460952548948569958162617750330001779372990521213418590137725259726450741103741783193402623334763523207442222181269470220616454421126328215138096104411600982523029892352200425580677351729446660909999175717788745567263052442650378502144|335544320"
def inputClause14637 : CNF.NClause := [(29,true),(1,true),(1024,false)]
theorem inputList14637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14637 = (containClause5 29 1) := by decide
  rw [he]
  exact input_contain 29 1 (by decide) v hb
mask_input "14637|179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216|536870914"
def inputClause14638 : CNF.NClause := [(29,true),(2,true),(1025,false)]
theorem inputList14638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14638 = (containClause5 29 2) := by decide
  rw [he]
  exact input_contain 29 2 (by decide) v hb
mask_input "14638|359538626972463181545861038157804946723595395788461314546860162315465351611001926265416954644815072042240227759742786715317579537628833244985694861278948248755535786849730970552604439202492188238906165904170011537676301364684925762947826221081654474326701021369172596479894491876959432609670712659248448274432|536870916"
def inputClause14641 : CNF.NClause := [(29,true),(5,true),(1028,false)]
theorem inputList14641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14641 = (containClause5 29 5) := by decide
  rw [he]
  exact input_contain 29 5 (by decide) v hb
mask_input "14641|2876309015779705452366888305262439573788763166307690516374881298523722812888015410123335637158520576337921822077942293722540636301030665959885558890231585990044286294797847764420835513619937505911249327233360092301410410917479406103582609768653235794613608170953380771839155935015675460877365701273987586195456|536870944"
def inputClause14644 : CNF.NClause := [(29,true),(8,true),(1031,false)]
theorem inputList14644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14644 = (containClause5 29 8) := by decide
  rw [he]
  exact input_contain 29 8 (by decide) v hb
mask_input "14644|23010472126237643618935106442099516590310105330461524130999050388189782503104123280986685097268164610703374576623538349780325090408245327679084471121852687920354290358382782115366684108959500047289994617866880738411283287339835248828660878149225886356908865367627046174713247480125403687018925610191900689563648|536871168"
def inputClause14646 : CNF.NClause := [(29,true),(10,true),(1033,false)]
theorem inputList14646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14646 = (containClause5 29 10) := by decide
  rw [he]
  exact input_contain 29 10 (by decide) v hb
mask_input "14646|92041888504950574475740425768398066361240421321846096523996201552759130012416493123946740389072658442813498306494153399121300361632981310716337884487410751681417161433531128461466736435838000189159978471467522953645133149359340995314643512596903545427635461470508184698852989920501614748075702440767602758254592|536871936"
def inputClause14647 : CNF.NClause := [(29,true),(11,true),(1034,false)]
theorem inputList14647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14647 = (containClause5 29 11) := by decide
  rw [he]
  exact input_contain 29 11 (by decide) v hb
mask_input "14647|184083777009901148951480851536796132722480842643692193047992403105518260024832986247893480778145316885626996612988306798242600723265962621432675768974821503362834322867062256922933472871676000378319956942935045907290266298718681990629287025193807090855270922941016369397705979841003229496151404881535205516509184|536872960"
end Percolation.MaskChain
