import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause13942 : CNF.NClause := [(5,true),(27,true),(306,false)]
theorem inputList13942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13942
  have he : decodeClause inputClause13942 = containClause5 5 27 := by decide
  rw [he]
  exact input_contain 5 27 (by decide) v hb
mask_input "13942|130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064|134217760"
def inputClause13943 : CNF.NClause := [(5,true),(28,true),(307,false)]
theorem inputList13943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13943
  have he : decodeClause inputClause13943 = containClause5 5 28 := by decide
  rw [he]
  exact input_contain 5 28 (by decide) v hb
mask_input "13943|260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128|268435488"
def inputClause13950 : CNF.NClause := [(6,true),(4,true),(314,false)]
theorem inputList13950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13950 = (containClause5 6 4) := by decide
  rw [he]
  exact input_contain 6 4 (by decide) v hb
mask_input "13950|33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384|80"
def inputClause13980 : CNF.NClause := [(7,true),(4,true),(345,false)]
theorem inputList13980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13980
  have he : decodeClause inputClause13980 = containClause5 7 4 := by decide
  rw [he]
  exact input_contain 7 4 (by decide) v hb
mask_input "13980|71671831749689734737838152978190216899892655911508785116799651230841339877765150252188079784691427704832|144"
def inputClause14009 : CNF.NClause := [(8,true),(3,true),(375,false)]
theorem inputList14009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14009
  have he : decodeClause inputClause14009 = containClause5 8 3 := by decide
  rw [he]
  exact input_contain 8 3 (by decide) v hb
mask_input "14009|76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568|264"
def inputClause14010 : CNF.NClause := [(8,true),(4,true),(376,false)]
theorem inputList14010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14010
  have he : decodeClause inputClause14010 = containClause5 8 4 := by decide
  rw [he]
  exact input_contain 8 4 (by decide) v hb
mask_input "14010|153914086704665934422965000391185991426092731525255651046673021110334850669910978950836977558144201721900890587136|272"
def inputClause14020 : CNF.NClause := [(8,true),(15,true),(387,false)]
theorem inputList14020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14020 = (containClause5 8 15) := by decide
  rw [he]
  exact input_contain 8 15 (by decide) v hb
mask_input "14020|315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528|33024"
def inputClause14022 : CNF.NClause := [(8,true),(17,true),(389,false)]
theorem inputList14022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14022
  have he : decodeClause inputClause14022 = containClause5 8 17 := by decide
  rw [he]
  exact input_contain 8 17 (by decide) v hb
mask_input "14022|1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112|131328"
def inputClause14025 : CNF.NClause := [(8,true),(20,true),(392,false)]
theorem inputList14025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14025
  have he : decodeClause inputClause14025 = containClause5 8 20 := by decide
  rw [he]
  exact input_contain 8 20 (by decide) v hb
mask_input "14025|10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896|1048832"
def inputClause14028 : CNF.NClause := [(8,true),(23,true),(395,false)]
theorem inputList14028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14028
  have he : decodeClause inputClause14028 = containClause5 8 23 := by decide
  rw [he]
  exact input_contain 8 23 (by decide) v hb
mask_input "14028|80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168|8388864"
def inputClause14032 : CNF.NClause := [(8,true),(27,true),(399,false)]
theorem inputList14032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14032 = (containClause5 8 27) := by decide
  rw [he]
  exact input_contain 8 27 (by decide) v hb
mask_input "14032|1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688|134217984"
def inputClause14033 : CNF.NClause := [(8,true),(28,true),(400,false)]
theorem inputList14033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14033
  have he : decodeClause inputClause14033 = containClause5 8 28 := by decide
  rw [he]
  exact input_contain 8 28 (by decide) v hb
mask_input "14033|2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376|268435712"
def inputClause14040 : CNF.NClause := [(9,true),(4,true),(407,false)]
theorem inputList14040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14040
  have he : decodeClause inputClause14040 = containClause5 9 4 := by decide
  rw [he]
  exact input_contain 9 4 (by decide) v hb
mask_input "14040|330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128|528"
def inputClause14069 : CNF.NClause := [(10,true),(3,true),(437,false)]
theorem inputList14069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14069
  have he : decodeClause inputClause14069 = containClause5 10 3 := by decide
  rw [he]
  exact input_contain 10 3 (by decide) v hb
mask_input "14069|354901720847464302026037015570314714039863945648104521621821386318671527399120079749116723981329865996466075003059657194108692201472|1032"
def inputClause14070 : CNF.NClause := [(10,true),(4,true),(438,false)]
theorem inputList14070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14070
  have he : decodeClause inputClause14070 = containClause5 10 4 := by decide
  rw [he]
  exact input_contain 10 4 (by decide) v hb
mask_input "14070|709803441694928604052074031140629428079727891296209043243642772637343054798240159498233447962659731992932150006119314388217384402944|1040"
def inputClause14080 : CNF.NClause := [(10,true),(15,true),(449,false)]
theorem inputList14080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14080
  have he : decodeClause inputClause14080 = containClause5 10 15 := by decide
  rw [he]
  exact input_contain 10 15 (by decide) v hb
mask_input "14080|1453677448591213781098647615776009068707282721374636120562980398361278576226795846652382101427527131121525043212532355867069203257229312|33792"
def inputClause14082 : CNF.NClause := [(10,true),(17,true),(451,false)]
theorem inputList14082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14082
  have he : decodeClause inputClause14082 = containClause5 10 17 := by decide
  rw [he]
  exact input_contain 10 17 (by decide) v hb
mask_input "14082|5814709794364855124394590463104036274829130885498544482251921593445114304907183386609528405710108524486100172850129423468276813028917248|132096"
def inputClause14085 : CNF.NClause := [(10,true),(20,true),(454,false)]
theorem inputList14085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14085
  have he : decodeClause inputClause14085 = containClause5 10 20 := by decide
  rw [he]
  exact input_contain 10 20 (by decide) v hb
mask_input "14085|46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984|1049600"
def inputClause14088 : CNF.NClause := [(10,true),(23,true),(457,false)]
theorem inputList14088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14088
  have he : decodeClause inputClause14088 = containClause5 10 23 := by decide
  rw [he]
  exact input_contain 10 23 (by decide) v hb
mask_input "14088|372141426839350727961253789638658321589064376671906846864122981980487315514059736743009817965446945567110411062408283101969716033850703872|8389632"
def inputClause14092 : CNF.NClause := [(10,true),(27,true),(461,false)]
theorem inputList14092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14092
  have he : decodeClause inputClause14092 = containClause5 10 27 := by decide
  rw [he]
  exact input_contain 10 27 (by decide) v hb
mask_input "14092|5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456541611261952|134218752"
def inputClause14099 : CNF.NClause := [(11,true),(3,true),(468,false)]
theorem inputList14099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14099
  have he : decodeClause inputClause14099 = containClause5 11 3 := by decide
  rw [he]
  exact input_contain 11 3 (by decide) v hb
mask_input "14099|762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529856|2056"
def inputClause14100 : CNF.NClause := [(11,true),(4,true),(469,false)]
theorem inputList14100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14100
  have he : decodeClause inputClause14100 = containClause5 11 4 := by decide
  rw [he]
  exact input_contain 11 4 (by decide) v hb
mask_input "14100|1524291284333980581729295522359944485228807686848130444755447734192076044345588681699368214386470689042884243711624327585667956874652483059712|2064"
def inputClause14110 : CNF.NClause := [(11,true),(15,true),(480,false)]
theorem inputList14110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14110
  have he : decodeClause inputClause14110 = containClause5 11 15 := by decide
  rw [he]
  exact input_contain 11 15 (by decide) v hb
mask_input "14110|3121748550315992231381597229793166305748598142664971150859156959625371738819765620120306103063491971159826931121406622895447975679288285306290176|34816"
def inputClause14112 : CNF.NClause := [(11,true),(17,true),(482,false)]
theorem inputList14112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14112 = (containClause5 11 17) := by decide
  rw [he]
  exact input_contain 11 17 (by decide) v hb
mask_input "14112|12486994201263968925526388919172665222994392570659884603436627838501486955279062480481224412253967884639307724485626491581791902717153141225160704|133120"
def inputClause14115 : CNF.NClause := [(11,true),(20,true),(485,false)]
theorem inputList14115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14115 = (containClause5 11 20) := by decide
  rw [he]
  exact input_contain 11 20 (by decide) v hb
mask_input "14115|99895953610111751404211111353381321783955140565279076827493022708011895642232499843849795298031743077114461795885011932654335221737225129801285632|1050624"
def inputClause14118 : CNF.NClause := [(11,true),(23,true),(488,false)]
theorem inputList14118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14118
  have he : decodeClause inputClause14118 = containClause5 11 23 := by decide
  rw [he]
  exact input_contain 11 23 (by decide) v hb
mask_input "14118|799167628880894011233688890827050574271641124522232614619944181664095165137859998750798362384253944616915694367080095461234681773897801038410285056|8390656"
def inputClause14122 : CNF.NClause := [(11,true),(27,true),(492,false)]
theorem inputList14122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14122
  have he : decodeClause inputClause14122 = containClause5 11 27 := by decide
  rw [he]
  exact input_contain 11 27 (by decide) v hb
mask_input "14122|12786682062094304179739022253232809188346257992355721833919106906625522642205759980012773798148063113870651109873281527379754908382364816614564560896|134219776"
def inputClause14123 : CNF.NClause := [(11,true),(28,true),(493,false)]
theorem inputList14123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14123
  have he : decodeClause inputClause14123 = containClause5 11 28 := by decide
  rw [he]
  exact input_contain 11 28 (by decide) v hb
mask_input "14123|25573364124188608359478044506465618376692515984711443667838213813251045284411519960025547596296126227741302219746563054759509816764729633229129121792|268437504"
def inputClause14130 : CNF.NClause := [(12,true),(4,true),(500,false)]
theorem inputList14130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14130 = (containClause5 12 4) := by decide
  rw [he]
  exact input_contain 12 4 (by decide) v hb
mask_input "14130|3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376|4112"
def inputClause14160 : CNF.NClause := [(13,true),(4,true),(531,false)]
theorem inputList14160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14160 = (containClause5 13 4) := by decide
  rw [he]
  exact input_contain 13 4 (by decide) v hb
mask_input "14160|7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970101818523648|8208"
def inputClause14190 : CNF.NClause := [(14,true),(4,true),(562,false)]
theorem inputList14190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14190 = (containClause5 14 4) := by decide
  rw [he]
  exact input_contain 14 4 (by decide) v hb
mask_input "14190|15095849699286165408966218323953075563667684881665761713504825200982496649568595408344506900710635070165873500123055379599082338519699170530245737005730784174597581307904|16400"
def inputClause14217 : CNF.NClause := [(15,true),(1,true),(590,false)]
theorem inputList14217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14217 = (containClause5 15 1) := by decide
  rw [he]
  exact input_contain 15 1 (by decide) v hb
mask_input "14217|4052261297735344686047273304385899561535592023674254785152009111026028136145418111718463914987406049109568248643848426935932764722081811824108276205189417663145685354884286644224|32770"
def inputClause14218 : CNF.NClause := [(15,true),(2,true),(591,false)]
theorem inputList14218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14218 = (containClause5 15 2) := by decide
  rw [he]
  exact input_contain 15 2 (by decide) v hb
mask_input "14218|8104522595470689372094546608771799123071184047348509570304018222052056272290836223436927829974812098219136497287696853871865529444163623648216552410378835326291370709768573288448|32772"
def inputClause14220 : CNF.NClause := [(15,true),(4,true),(593,false)]
theorem inputList14220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14220 = (containClause5 15 4) := by decide
  rw [he]
  exact input_contain 15 4 (by decide) v hb
mask_input "14220|32418090381882757488378186435087196492284736189394038281216072888208225089163344893747711319899248392876545989150787415487462117776654494592866209641515341305165482839074293153792|32784"
def inputClause14221 : CNF.NClause := [(15,true),(5,true),(594,false)]
theorem inputList14221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14221 = (containClause5 15 5) := by decide
  rw [he]
  exact input_contain 15 5 (by decide) v hb
mask_input "14221|64836180763765514976756372870174392984569472378788076562432145776416450178326689787495422639798496785753091978301574830974924235553308989185732419283030682610330965678148586307584|32800"
def inputClause14224 : CNF.NClause := [(15,true),(8,true),(597,false)]
theorem inputList14224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14224 = (containClause5 15 8) := by decide
  rw [he]
  exact input_contain 15 8 (by decide) v hb
mask_input "14224|518689446110124119814050982961395143876555779030304612499457166211331601426613518299963381118387974286024735826412598647799393884426471913485859354264245460882647725425188690460672|33024"
def inputClause14226 : CNF.NClause := [(15,true),(10,true),(599,false)]
theorem inputList14226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14226 = (containClause5 15 10) := by decide
  rw [he]
  exact input_contain 15 10 (by decide) v hb
mask_input "14226|2074757784440496479256203931845580575506223116121218449997828664845326405706454073199853524473551897144098943305650394591197575537705887653943437417056981843530590901700754761842688|33792"
def inputClause14227 : CNF.NClause := [(15,true),(11,true),(600,false)]
theorem inputList14227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14227 = (containClause5 15 11) := by decide
  rw [he]
  exact input_contain 15 11 (by decide) v hb
mask_input "14227|4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376|34816"
def inputClause14250 : CNF.NClause := [(16,true),(4,true),(624,false)]
theorem inputList14250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14250 = (containClause5 16 4) := by decide
  rw [he]
  exact input_contain 16 4 (by decide) v hb
mask_input "14250|69617318994479297159441705409245167921344429126717528237597542082203295398081625160307507496908132931192662194421301381083506846944815643283884602656894137393981852330936660004926669193216|65552"
def inputClause14277 : CNF.NClause := [(17,true),(1,true),(652,false)]
theorem inputList14277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14277 = (containClause5 17 1) := by decide
  rw [he]
  exact input_contain 17 1 (by decide) v hb
mask_input "14277|18687756769780511615554238896948393266762663965690101475652372553315431084886742575128218875155953253493318900013442692344580934538753794040842900765582189315080170186179645235539452691442089066496|131074"
end Percolation.MaskChain
