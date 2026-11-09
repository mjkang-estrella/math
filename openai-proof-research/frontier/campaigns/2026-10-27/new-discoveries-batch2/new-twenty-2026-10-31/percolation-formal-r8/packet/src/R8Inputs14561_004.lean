import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9343 : CNF.NClause := [(343,true),(347,true),(351,true),(360,true),(364,false),(370,true)]
theorem inputList9343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) inputClause9343 (by decide) v hb
mask_input "9343|37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616|2407261038945695974911113469163011214542378030304793827949557467396710755663920312021796185180833225797674205184"
def inputClause9361 : CNF.NClause := [(356,true),(357,true),(358,true),(359,true),(360,false),(371,true)]
theorem inputList9361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) inputClause9361 (by decide) v hb
mask_input "9361|2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976|4812016968192160919368802650284052235528562562553840645087319994983775529395763037629402766502992024468495269888"
def inputClause9362 : CNF.NClause := [(356,true),(357,true),(358,true),(359,false),(360,true),(371,true)]
theorem inputList9362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) inputClause9362 (by decide) v hb
mask_input "9362|1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488|4813191239483547835982747390582446904042250403828294805022673640469541633908320341851134616002184408820011237376"
def inputClause9363 : CNF.NClause := [(356,true),(357,true),(358,false),(359,true),(360,true),(371,true)]
theorem inputList9363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) inputClause9363 (by decide) v hb
mask_input "9363|587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744|4813778375129241294289719760731644238299094324465521884990350463212424686164598993962000540751780600995769221120"
def inputClause9365 : CNF.NClause := [(356,false),(357,true),(358,true),(359,true),(360,true),(371,true)]
theorem inputList9365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) inputClause9365 (by decide) v hb
mask_input "9365|146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936|4814218726863511388019949038343542238991727264943442194966108080269586975356807983045149984313977745127587708928"
def inputClause9368 : CNF.NClause := [(345,true),(347,true),(354,true),(356,false),(363,true),(368,true)]
theorem inputList9368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) inputClause9368 (by decide) v hb
mask_input "9368|146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936|620052296189306561755682339877474699569317437414902695908630201904189527602973433657096916810827623068554231808"
def inputClause9374 : CNF.NClause := [(343,true),(349,true),(355,true),(356,false),(362,true),(367,true)]
theorem inputList9374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) inputClause9374 (by decide) v hb
mask_input "9374|146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936|310082177549123600827972474914828049986720209791210169947080159079444474018936159734758106436785494057885368320"
def inputClause9376 : CNF.NClause := [(343,true),(349,false),(355,true),(356,true),(362,true),(367,true)]
theorem inputList9376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) inputClause9376 (by decide) v hb
mask_input "9376|1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312|310227814711238970368959762041679732507460791668022355798437495970745543621567778520070552614907987038981586944"
def inputClause9421 : CNF.NClause := [(341,true),(342,true),(343,true),(344,true),(345,false),(371,true)]
theorem inputList9421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) inputClause9421 (by decide) v hb
mask_input "9421|71671831749689734737838152978190216899892655911508785116799651230841339877765150252188079784691427704832|4809815276713152716051782578947830649118726203813604012248017956697637112348474227618483910118331101957616304128"
def inputClause9426 : CNF.NClause := [(341,true),(350,true),(354,true),(358,true),(362,true),(370,false)]
theorem inputList9426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) inputClause9426 (by decide) v hb
mask_input "9426|2404907604760405225358828131112281116032698930082119547604265954848982041717359046106827774346003151904701415424|10020299932750106789836097606459378981228748680967214698908595439259667973214332486779801820293125667771383808"
def inputClause9427 : CNF.NClause := [(341,true),(350,true),(354,true),(358,true),(362,false),(370,true)]
theorem inputList9427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) inputClause9427 (by decide) v hb
mask_input "9427|9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904|2405533734362059999237106306331583146904424948567453482820345386402112873590114944819752780172757202760345059328"
def inputClause9428 : CNF.NClause := [(341,true),(350,true),(354,true),(358,false),(362,true),(370,true)]
theorem inputList9428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) inputClause9428 (by decide) v hb
mask_input "9428|587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744|2414340769047461873841691858569543160757083758125859682335497727545358657434294726482741651416700085396714815488"
def inputClause9451 : CNF.NClause := [(341,true),(346,true),(351,true),(356,true),(361,false),(366,true)]
theorem inputList9451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) inputClause9451 (by decide) v hb
mask_input "9451|4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952|150458244029333655039770969164798025007458612448020395766302606440741578127420278269631752259045021215426084864"
def inputClause9458 : CNF.NClause := [(397,true),(398,true),(399,true),(400,false),(401,true),(402,true)]
theorem inputList9458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) inputClause9458 (by decide) v hb
mask_input "9458|2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376|17752967911847496553884444307520706636016727325700911650710783076216952401365783213078811803800947591121834307312639016960"
def inputClause9463 : CNF.NClause := [(376,true),(381,true),(386,true),(391,true),(396,false),(397,true)]
theorem inputList9463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) inputClause9463 (by decide) v hb
mask_input "9463|161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336|327987378743648898938846687638608350451200810747494711500486134506638029076014888191717729925921456552731194120703311872"
def inputClause9467 : CNF.NClause := [(376,false),(381,true),(386,true),(391,true),(396,true),(397,true)]
theorem inputList9467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) inputClause9467 (by decide) v hb
mask_input "9467|153914086704665934422965000391185991426092731525255651046673021110334850669910978950836977558144201721900890587136|489377842209993981126407212923796201410815996706589655796751297617407395117216792945091613668952512873273420468109443072"
def inputClause9470 : CNF.NClause := [(374,true),(379,true),(384,true),(389,false),(394,true),(397,true)]
theorem inputList9470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) inputClause9470 (by decide) v hb
mask_input "9470|1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112|363169560903383228393534902064276915725849222120915105297600555359356977830407816970981636476339122150978895869005266944"
def inputClause9483 : CNF.NClause := [(373,true),(378,true),(383,false),(388,true),(393,true),(397,true)]
theorem inputList9483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) inputClause9483 (by decide) v hb
mask_input "9483|19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408|343586128928167515478052724403878926022509959070976236624069686011234773978714689914320573945128891732665898916649107456"
def inputClause9484 : CNF.NClause := [(373,true),(378,false),(383,true),(388,true),(393,true),(397,true)]
theorem inputList9484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) inputClause9484 (by decide) v hb
mask_input "9484|615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544|343605214274918894053921172063927433085446794569685368324799473465852455500197758875710477730346101613679414627081912320"
def inputClause9488 : CNF.NClause := [(392,true),(393,true),(394,true),(395,false),(396,true),(402,true)]
theorem inputList9488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) inputClause9488 (by decide) v hb
mask_input "9488|80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168|10560998524832005052225575676121693095403132676141394601303516977726789297857940354598588612829313709036682113497916506112"
def inputClause9504 : CNF.NClause := [(375,true),(378,true),(386,true),(389,true),(392,true),(400,false)]
theorem inputList9504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 8) (closed_mem 8 8) inputClause9504 (by decide) v hb
mask_input "9504|2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376|11506078422737358926690383051743695568044701284267774077470611702634747264105200097938244512825407016023283927177232384"
def inputClause9511 : CNF.NClause := [(373,true),(379,true),(385,true),(391,true),(392,false),(398,true)]
theorem inputList9511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 9) (closed_mem 8 9) inputClause9511 (by decide) v hb
mask_input "9511|10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896|650685980879212905122293254804399816763267151315910028976662871496010370805166629063599168483612156813919645076662779904"
def inputClause9521 : CNF.NClause := [(382,false),(383,true),(384,true),(385,true),(386,true),(402,true)]
theorem inputList9521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) inputClause9521 (by decide) v hb
mask_input "9521|9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704|10329295027394107317217768780812798574422361269361422542172647038363122330980651007598167020117462962610918737600917274624"
def inputClause9522 : CNF.NClause := [(376,true),(379,true),(382,true),(390,true),(393,true),(400,false)]
theorem inputList9522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) inputClause9522 (by decide) v hb
mask_input "9522|2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376|22706791297452660639485603542711278129100034589189440943264624131386590184481296813638028462175455935830316487429586944"
def inputClause9526 : CNF.NClause := [(376,true),(379,false),(382,true),(390,true),(393,true),(400,true)]
theorem inputList9526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) inputClause9526 (by decide) v hb
mask_input "9526|1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088|2604955438071667612967929391825720022970874418676560751728715607287865329522517132155451775046492822218119713253052383232"
def inputClause9529 : CNF.NClause := [(374,true),(378,true),(382,true),(391,true),(395,false),(401,true)]
theorem inputList9529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 12) (closed_mem 8 12) inputClause9529 (by decide) v hb
mask_input "9529|80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168|5169553717603373266101034428500118829670376623113993201533000030070729476773992253641865127264619275415597112064036831232"
def inputClause9537 : CNF.NClause := [(375,true),(381,true),(382,false),(388,true),(394,true),(398,true)]
theorem inputList9537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 13) (closed_mem 8 13) inputClause9537 (by decide) v hb
mask_input "9537|9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704|686545558173795307437618741067415040484430725062364513550990081148763542029214169800098077426885409811970647882050043904"
def inputClause9539 : CNF.NClause := [(375,false),(381,true),(382,true),(388,true),(394,true),(398,true)]
theorem inputList9539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 13) (closed_mem 8 13) inputClause9539 (by decide) v hb
mask_input "9539|76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568|686555331718301053724454599344939880794886281950816367284831544885604048292231709147261455574960351968779988588602327040"
def inputClause9548 : CNF.NClause := [(387,true),(388,true),(389,true),(390,false),(391,true),(402,true)]
theorem inputList9548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) inputClause9548 (by decide) v hb
mask_input "9548|2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224|10336249481487770942798736031390473922258957843342659693509539912148971700873320265271081638111450150221521107441206427648"
def inputClause9562 : CNF.NClause := [(374,true),(380,false),(386,true),(387,true),(393,true),(398,true)]
theorem inputList9562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 17) (closed_mem 8 17) inputClause9562 (by decide) v hb
mask_input "9562|2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176|666209159247159530687697615754478320012786088108212653575582506547241941296187504495537151546838543190808896535330291712"
def inputClause9566 : CNF.NClause := [(375,true),(379,true),(383,true),(387,false),(396,true),(401,true)]
theorem inputList9566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 18) (closed_mem 8 18) inputClause9566 (by decide) v hb
mask_input "9566|315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528|5325911382827084153065382026978765387692847859368126692609602793732467281116851406772270330387720964020085331665356849152"
def inputClause9578 : CNF.NClause := [(377,true),(378,true),(379,true),(380,false),(381,true),(402,true)]
theorem inputList9578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 20) (closed_mem 8 20) inputClause9578 (by decide) v hb
mask_input "9578|2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176|10329006592395622773256660144402065491874428771582544213082585573121561563470495594423613151621519000376891895331956981760"
def inputClause9587 : CNF.NClause := [(376,false),(377,true),(383,true),(389,true),(395,true),(398,true)]
theorem inputList9587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 21) (closed_mem 8 21) inputClause9587 (by decide) v hb
mask_input "9587|153914086704665934422965000391185991426092731525255651046673021110334850669910978950836977558144201721900890587136|727538651241499270746995181859102539475877697944972290511633356908737350319511585156416620937277641138077426328801378304"
def inputClause9591 : CNF.NClause := [(374,true),(377,true),(385,false),(388,true),(396,true),(400,true)]
theorem inputList9591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) inputClause9591 (by decide) v hb
mask_input "9591|78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632|2744271273873177773675163036566053294464674389418023361354477594033203528194651731963483455503424110375353900545892941824"
def inputClause9592 : CNF.NClause := [(374,true),(377,false),(385,true),(388,true),(396,true),(400,true)]
theorem inputList9592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) inputClause9592 (by decide) v hb
mask_input "9592|307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272|2744349770057397153301718748716252799320301696711101241736511397273969798968493386562748382361978763918232070000092381184"
def inputClause9594 : CNF.NClause := [(375,true),(377,true),(384,true),(391,true),(393,true),(399,false)]
theorem inputList9594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 23) (closed_mem 8 23) inputClause9594 (by decide) v hb
mask_input "9594|1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688|25257070757105622839906922116693034414034678104197164453282472754674283492656386779363921761825126286261353294013136896"
def inputClause9604 : CNF.NClause := [(373,true),(377,false),(386,true),(390,true),(394,true),(401,true)]
theorem inputList9604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 24) (closed_mem 8 24) inputClause9604 (by decide) v hb
mask_input "9604|307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272|5207526766179540788694888858666005623832807589203386734079674630312859211000013676985827454165232185519592396948521353216"
def inputClause9607 : CNF.NClause := [(372,true),(373,true),(374,true),(375,true),(376,false),(402,true)]
theorem inputList9607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) inputClause9607 (by decide) v hb
mask_input "9607|153914086704665934422965000391185991426092731525255651046673021110334850669910978950836977558144201721900890587136|10328999656642090644247990209541735364055690133278829856249810282418547779006287281560124179530217786503801802173074898944"
def inputClause9608 : CNF.NClause := [(372,true),(373,true),(374,true),(375,false),(376,true),(402,true)]
theorem inputList9608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) inputClause9608 (by decide) v hb
mask_input "9608|76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568|10328999733599133996580957421024235559648685846325195618877635805755058334173712616515613654948706565575902663123520192512"
def inputClause9618 : CNF.NClause := [(372,true),(379,true),(386,true),(388,true),(395,true),(399,false)]
theorem inputList9618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) inputClause9618 (by decide) v hb
mask_input "9618|1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688|81484589746467839380089340082412647285960773683970466083003634561212854698189757701672493738233568082814489509884854272"
end Percolation.MaskChain
