import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9274 : CNF.NClause := [(366,true),(367,false),(368,true),(369,true),(370,true),(371,true)]
theorem inputList9274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) inputClause9274 (by decide) v hb
mask_input "9274|300613450595050653169853516389035139504087366260264943450533244356122755214669880763353471793250393988087676928|9168710243149044921680532249865571754874664670938080775241263952861744034047431363282280889694137016636674146304"
def inputClause9286 : CNF.NClause := [(343,true),(348,false),(353,true),(358,true),(363,true),(366,true)]
theorem inputList9286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 2) (closed_mem 7 2) inputClause9286 (by decide) v hb
mask_input "9286|573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656|169700567512295308709541544144730261470973661651703434784787952603830005157874137360004375828744365972406665216"
def inputClause9299 : CNF.NClause := [(342,false),(347,true),(352,true),(357,true),(362,true),(366,true)]
theorem inputList9299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) inputClause9299 (by decide) v hb
mask_input "9299|8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104|160003924133258347694956260292466706098599159474959610351569614989594210892796565210797783091493947162507608064"
def inputClause9301 : CNF.NClause := [(361,true),(362,true),(363,true),(364,true),(365,false),(371,true)]
theorem inputList9301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) inputClause9301 (by decide) v hb
mask_input "9301|75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232|4880271487004025447554340680128242342886668336631488691329750638843930354188156345517566518643549364900360880128"
def inputClause9304 : CNF.NClause := [(361,true),(362,false),(363,true),(364,true),(365,true),(371,true)]
theorem inputList9304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) inputClause9304 (by decide) v hb
mask_input "9304|9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904|4946030679321692777935246136838343779653187448000921647709554786046832206891365381934550090598322888585255059456"
def inputClause9307 : CNF.NClause := [(345,true),(349,true),(353,true),(357,true),(361,false),(370,true)]
theorem inputList9307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) inputClause9307 (by decide) v hb
mask_input "9307|4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952|2405220738993319619809897746002642829090334561095796929486441252525209587531285002048279584066582468752343826432"
def inputClause9315 : CNF.NClause := [(343,true),(350,true),(352,false),(359,true),(361,true),(368,true)]
theorem inputList9315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) inputClause9315 (by decide) v hb
mask_input "9315|9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496|607100569063609816903376029550477168211108960430953832736154732929828227625337340561461824148035766032298672128"
def inputClause9317 : CNF.NClause := [(343,false),(350,true),(352,true),(359,true),(361,true),(368,true)]
theorem inputList9317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) inputClause9317 (by decide) v hb
mask_input "9317|17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208|607109725140115839766988788374520132011317921717746527983453404085272967606506725059406541175228260362187964416"
def inputClause9318 : CNF.NClause := [(344,true),(347,true),(355,true),(358,true),(361,true),(369,false)]
theorem inputList9318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) inputClause9318 (by decide) v hb
mask_input "9318|1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712|5357935290195680654929197883114076949676825331648706494584033127238390624572150454827698186424284715216273408"
def inputClause9320 : CNF.NClause := [(344,true),(347,true),(355,true),(358,false),(361,true),(369,true)]
theorem inputList9320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) inputClause9320 (by decide) v hb
mask_input "9320|587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744|1207224602024704835027370893290057300709182369735481400329040187808846359226973021397375660609829668491808997376"
def inputClause9334 : CNF.NClause := [(351,true),(352,false),(353,true),(354,true),(355,true),(371,true)]
theorem inputList9334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) inputClause9334 (by decide) v hb
mask_input "9334|9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496|4809948232440537874865329689836489753107964060933610855513708689850648524961531224332523609768086691099222999040"
def inputClause9335 : CNF.NClause := [(351,false),(352,true),(353,true),(354,true),(355,true),(371,true)]
theorem inputList9335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) inputClause9335 (by decide) v hb
mask_input "9335|4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248|4809952819437769855008352911478280357281845654063589192075956165028327298807283401302139749805192911350596108288"
def inputClause9345 : CNF.NClause := [(343,true),(347,true),(351,false),(360,true),(364,true),(370,true)]
theorem inputList9345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) inputClause9345 (by decide) v hb
mask_input "9345|4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248|2444833133272845326414321937069850002806507357957348609318626647763547326220001870147599229117883304794812055552"
def inputClause9350 : CNF.NClause := [(344,true),(350,true),(351,true),(357,false),(363,true),(367,true)]
theorem inputList9350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) inputClause9350 (by decide) v hb
mask_input "9350|293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872|319408707589005164052371562545112231079023666292826963013955343294724203604884952648062399930027766335116673024"
def inputClause9382 : CNF.NClause := [(344,true),(348,false),(352,true),(356,true),(365,true),(370,true)]
theorem inputList9382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 18) (closed_mem 7 18) inputClause9382 (by decide) v hb
mask_input "9382|573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656|2480216961150971088358948414949496931915803388012777182337705980378916656697270472147190029649967131294122901504"
def inputClause9389 : CNF.NClause := [(342,false),(350,true),(353,true),(356,true),(364,true),(369,true)]
theorem inputList9389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) inputClause9389 (by decide) v hb
mask_input "9389|8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104|1240197909103551219545993345030127002801038535067802176255482476954281610630467717539822182501534914375980154880"
def inputClause9409 : CNF.NClause := [(344,true),(346,true),(353,true),(360,true),(362,false),(368,true)]
theorem inputList9409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) inputClause9409 (by decide) v hb
mask_input "9409|9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904|603593970941382434364026244537404478206619037320991331792726472393620891940812772261510833203509899413268987904"
def inputClause9415 : CNF.NClause := [(342,true),(346,true),(355,true),(359,true),(363,false),(370,true)]
theorem inputList9415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) inputClause9415 (by decide) v hb
mask_input "9415|18788340662190665823115844774314696219005460391266558965658327772257672200916867547709591987078149624255479808|2406155420310146292351830735585400529982703173708120904491747576376867393299798422093362150338564602747471003648"
def inputClause9419 : CNF.NClause := [(342,false),(346,true),(355,true),(359,true),(363,true),(370,true)]
theorem inputList9419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) inputClause9419 (by decide) v hb
mask_input "9419|8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104|2424943752013357989463729738129946103927931521612805474518807764549168661645547804920427960802132779285298020352"
def inputClause9423 : CNF.NClause := [(341,true),(342,true),(343,false),(344,true),(345,true),(371,true)]
theorem inputList9423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) inputClause9423 (by decide) v hb
mask_input "9423|17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208|4809815330467026528319083632326445382761388878733095945879606794297375535479479135942346599259390940476187082752"
def inputClause9429 : CNF.NClause := [(341,true),(350,true),(354,false),(358,true),(362,true),(370,true)]
theorem inputList9429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) inputClause9429 (by decide) v hb
mask_input "9429|36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984|2414891208715299491004478455584415661622874933723260069805194748866811518924555962836678455869446515561487925248"
def inputClause9446 : CNF.NClause := [(341,true),(347,true),(353,true),(359,false),(365,true),(367,true)]
theorem inputList9446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) inputClause9446 (by decide) v hb
mask_input "9446|1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488|375785452399557720148957154520952814973391736159159166066595993154451664694289312253579299404061998799527084032"
def inputClause9448 : CNF.NClause := [(341,true),(347,false),(353,true),(359,true),(365,true),(367,true)]
theorem inputList9448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) inputClause9448 (by decide) v hb
mask_input "9448|286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328|376959437003617638003962943466735570726211977862989679966809171441612845841487105414710140150935244385332232192"
def inputClause9646 : CNF.NClause := [(428,true),(429,false),(430,true),(431,true),(432,true),(433,true)]
theorem inputList9646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) inputClause9646 (by decide) v hb
mask_input "9646|1386334847060407429789207092071541851718218537687908287585239790307310653902812811519987203052069789048695605480701785914487078912|42283212835342426608570816308182026477405665399481202771349813604372974944035790751359609693088128565985215967161404470391855906816"
def inputClause9656 : CNF.NClause := [(405,true),(410,true),(415,true),(420,false),(425,true),(428,true)]
theorem inputList9656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) inputClause9656 (by decide) v hb
mask_input "9656|2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576|779900693491355590852565511100316121465135255418185067422795366269937873685499304116559954841218603721901766071783560788114931712"
def inputClause9659 : CNF.NClause := [(405,false),(410,true),(415,true),(420,true),(425,true),(428,true)]
theorem inputList9659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) inputClause9659 (by decide) v hb
mask_input "9659|82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032|782608296107524350332797687212604847547892422449021392761832877154282430505679330850141701698528372564226893727336553335809376256"
def inputClause9675 : CNF.NClause := [(423,true),(424,true),(425,false),(426,true),(427,true),(433,true)]
theorem inputList9675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) inputClause9675 (by decide) v hb
mask_input "9675|86645927941275464361825443254471365732388658605494267974077486894206915868925800719999200190754361815543475342543861619655442432|22766217566570128261069635215112351346185120048593618910188859681452867144560254139179789850120708567034048146253399640564467499008"
def inputClause9677 : CNF.NClause := [(423,false),(424,true),(425,true),(426,true),(427,true),(433,true)]
theorem inputList9677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) inputClause9677 (by decide) v hb
mask_input "9677|21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608|22831202012526084859341004297553204870484411542547739611169417796623522331461948489719789250263774338395705752760307536779209080832"
def inputClause9683 : CNF.NClause := [(407,false),(411,true),(415,true),(419,true),(423,true),(432,true)]
theorem inputList9683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 6) (closed_mem 9 6) inputClause9683 (by decide) v hb
mask_input "9683|330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128|11113784004704416207344224080418696227129830701982233857858355367150916262437794046319179637699847241025557851888312903735346987008"
def inputClause9690 : CNF.NClause := [(406,true),(409,true),(417,true),(420,true),(423,true),(431,false)]
theorem inputList9690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) inputClause9690 (by decide) v hb
mask_input "9690|5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648|24709115265434109693774428362475924119466067341009644484726423831965558266278654562090378605118287845854476220874329342536056832"
def inputClause9713 : CNF.NClause := [(407,false),(410,true),(413,true),(421,true),(424,true),(431,true)]
theorem inputList9713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) inputClause9713 (by decide) v hb
mask_input "9713|330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128|5594101520723473616809917449067896729854776593785810390200271994963863884396006516193398069127154314466280140086620966659903455232"
def inputClause9714 : CNF.NClause := [(405,true),(409,true),(413,true),(422,true),(426,true),(432,false)]
theorem inputList9714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) inputClause9714 (by decide) v hb
mask_input "9714|11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296|184145155410145329002318301025638270493060043846481475541522748290328435319093265654674584987159274142125309153016059863869947904"
def inputClause9729 : CNF.NClause := [(404,true),(411,true),(413,false),(420,true),(427,true),(430,true)]
theorem inputList9729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) inputClause9729 (by decide) v hb
mask_input "9729|21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192|3121966420897829946666352052079842410761637471891971742458309932137804837298924599952696897461127269370784929640180465734036488192"
def inputClause9740 : CNF.NClause := [(407,true),(409,true),(416,true),(418,false),(425,true),(430,true)]
theorem inputList9740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 16) (closed_mem 9 16) inputClause9740 (by decide) v hb
mask_input "9740|676921312041214565326761275425557544784286395355423968547480366360991530225982818124993751490268451683933401113623918903558144|2859486505030022603203068697504681540482621376591857109839742149222406657571586010242869417705792606314067788632255901986751250432"
def inputClause9748 : CNF.NClause := [(405,true),(411,false),(417,true),(418,true),(424,true),(429,true)]
theorem inputList9748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 17) (closed_mem 9 17) inputClause9748 (by decide) v hb
mask_input "9748|5288447750321988791615322464262168318627237463714249754277190362195246329890490766601513683517722278780729696200186866434048|1430673275631103082599184824601329374997969275134273928060252164885055008433338590646092521923333677598403849202545655730589925376"
def inputClause9793 : CNF.NClause := [(403,true),(404,true),(405,true),(406,true),(407,false),(433,true)]
theorem inputList9793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 25) (closed_mem 9 25) inputClause9793 (by decide) v hb
mask_input "9793|330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128|22181357862836504247056344231854970267852921522571227740870658184596093247322719626340738604390559018395669459999609211361492467712"
def inputClause9796 : CNF.NClause := [(403,true),(404,false),(405,true),(406,true),(407,true),(433,true)]
theorem inputList9796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 25) (closed_mem 9 25) inputClause9796 (by decide) v hb
mask_input "9796|41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016|22181358152048490592790106273317917532190251447498276537743691621629941179875253292226952402910838585771106580820764472309211725824"
def inputClause9802 : CNF.NClause := [(403,true),(412,false),(416,true),(420,true),(424,true),(432,true)]
theorem inputList9802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 26) (closed_mem 9 26) inputClause9802 (by decide) v hb
mask_input "9802|10576895500643977583230644928524336637254474927428499508554380724390492659780981533203027367035444557561459392400373732868096|11136878676688071357092476910867482492201370842623920329169071960107897755485606795631658004992931960458095949958844495563044421632"
def inputClause9818 : CNF.NClause := [(403,true),(409,true),(415,true),(421,false),(427,true),(429,true)]
theorem inputList9818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 29) (closed_mem 9 29) inputClause9818 (by decide) v hb
mask_input "9818|5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152|1733004516759451044249641331326824950907045859356317058673844844872798842456557711009670835449607225539002345195665861211668348928"
def inputClause9825 : CNF.NClause := [(403,true),(408,true),(413,false),(418,true),(423,true),(428,true)]
theorem inputList9825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 30) (closed_mem 9 30) inputClause9825 (by decide) v hb
mask_input "9825|21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192|715506508541531610494254337287475733632125542933012441669694134537638174179836051204193777551587019386305104055537883086399209472"
end Percolation.MaskChain
