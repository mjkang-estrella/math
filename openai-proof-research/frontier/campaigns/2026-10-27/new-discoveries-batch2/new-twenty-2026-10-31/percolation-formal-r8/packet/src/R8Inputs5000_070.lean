import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause9272 : CNF.NClause := [(366,true),(367,true),(368,true),(369,false),(370,true),(371,true)]
theorem inputList9272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) inputClause9272 (by decide) v hb
mask_input "9272|1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712|8266869891363892962170971700698466336362402572157285944889664219793375768403421720992220474314385834672411115520"
def inputClause9273 : CNF.NClause := [(366,true),(367,true),(368,false),(369,true),(370,true),(371,true)]
theorem inputList9273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) inputClause9273 (by decide) v hb
mask_input "9273|601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856|8868096792553994268510678733476536615370577304677815831790730708505621278832761482518927417900886622648586469376"
def inputClause9279 : CNF.NClause := [(345,true),(350,true),(355,false),(360,true),(365,true),(366,true)]
theorem inputList9279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) inputClause9279 (by decide) v hb
mask_input "9279|73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968|227810995699509562866525966547613971932598903701752107248516078627114893200332985265937125049955459011211952128"
def inputClause9280 : CNF.NClause := [(345,true),(350,false),(355,true),(360,true),(365,true),(366,true)]
theorem inputList9280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) inputClause9280 (by decide) v hb
mask_input "9280|2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624|227882094156605255083385901995368336627763597216416323963351943881135887809491728294987295625101872907495145472"
def inputClause9281 : CNF.NClause := [(345,false),(350,true),(355,true),(360,true),(365,true),(366,true)]
theorem inputList9281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) inputClause9281 (by decide) v hb
mask_input "9281|71671831749689734737838152978190216899892655911508785116799651230841339877765150252188079784691427704832|227884315983389495465162774978110660524487493888749580735690564670324043891027939014645113455575198341753995264"
def inputClause9292 : CNF.NClause := [(344,true),(349,false),(354,true),(359,true),(364,true),(366,true)]
theorem inputList9292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) inputClause9292 (by decide) v hb
mask_input "9292|1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312|189094409727065290834156330094942953189903640173274397844309283029598632708413334338332015760863534950769491968"
def inputClause9302 : CNF.NClause := [(361,true),(362,true),(363,true),(364,false),(365,true),(371,true)]
theorem inputList9302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) inputClause9302 (by decide) v hb
mask_input "9302|37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616|4917848168328406779200572369676871735324679257414021809261067294388445698589990080612985702617705664148871839744"
def inputClause9303 : CNF.NClause := [(361,true),(362,true),(363,false),(364,true),(365,true),(371,true)]
theorem inputList9303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) inputClause9303 (by decide) v hb
mask_input "9303|18788340662190665823115844774314696219005460391266558965658327772257672200916867547709591987078149624255479808|4936636508990597445023688214451186431543684717805288368226725622160703370790906948160695294604783813773127319552"
def inputClause9305 : CNF.NClause := [(361,false),(362,true),(363,true),(364,true),(365,true),(371,true)]
theorem inputList9305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) inputClause9305 (by decide) v hb
mask_input "9305|4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952|4950727764487240444391025098031922453707938813098738287450969367989896624941594598821477488595092425991318929408"
def inputClause9328 : CNF.NClause := [(342,true),(348,false),(354,true),(360,true),(361,true),(367,true)]
theorem inputList9328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 9) (closed_mem 7 9) inputClause9328 (by decide) v hb
mask_input "9328|573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656|307695783280206962708924573543497106251044271433398584499233058292105976911198606571317470608764435194596818944"
def inputClause9347 : CNF.NClause := [(343,false),(347,true),(351,true),(360,true),(364,true),(370,true)]
theorem inputList9347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) inputClause9347 (by decide) v hb
mask_input "9347|17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208|2444837702352119369134911474252102362432834726114162968003677843741313292355419077675927806107969578873328238592"
def inputClause9351 : CNF.NClause := [(344,true),(350,true),(351,false),(357,true),(363,true),(367,true)]
theorem inputList9351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) inputClause9351 (by decide) v hb
mask_input "9351|4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248|319697688414619913062834525977920294033564033481462166435546279488486955887272101733879222267719642171622555648"
def inputClause9371 : CNF.NClause := [(345,false),(347,true),(354,true),(356,true),(363,true),(368,true)]
theorem inputList9371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) inputClause9371 (by decide) v hb
mask_input "9371|71671831749689734737838152978190216899892655911508785116799651230841339877765150252188079784691427704832|620199008428898176642690694576621054943311517681553554391764290790259059825703218919663145810146886421066022912"
def inputClause9375 : CNF.NClause := [(343,true),(349,true),(355,false),(356,true),(362,true),(367,true)]
theorem inputList9375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) inputClause9375 (by decide) v hb
mask_input "9375|73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968|310155569504835283116344021183477716768825699870863554943039761922304855550970991248616347030485018079855116288"
def inputClause9377 : CNF.NClause := [(343,false),(349,true),(355,true),(356,true),(362,true),(367,true)]
theorem inputList9377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) inputClause9377 (by decide) v hb
mask_input "9377|17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208|310228943542589027982281882992589139003376964977352962061803085565252429372670853321187024577164595928967938048"
def inputClause9393 : CNF.NClause := [(346,true),(347,true),(348,false),(349,true),(350,true),(371,true)]
theorem inputList9393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 20) (closed_mem 7 20) inputClause9393 (by decide) v hb
mask_input "9393|573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656|4809819079799724933963332105484823054337110454367658316682928216879130548867071491531769166848314677146498891776"
def inputClause9400 : CNF.NClause := [(345,true),(346,false),(352,true),(358,true),(364,true),(367,true)]
theorem inputList9400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 21) (closed_mem 7 21) inputClause9400 (by decide) v hb
mask_input "9400|143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664|338786513231421153098838757208596052736922293832637725982806789798529930405626499674021112779295110606530543616"
def inputClause9412 : CNF.NClause := [(344,true),(346,false),(353,true),(360,true),(362,true),(368,true)]
theorem inputList9412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) inputClause9412 (by decide) v hb
mask_input "9412|143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664|612987997928814267896114691248255869935687967731312788257985402680447266358591450505065124820889404842541318144"
def inputClause9424 : CNF.NClause := [(341,true),(342,false),(343,true),(344,true),(345,true),(371,true)]
theorem inputList9424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) inputClause9424 (by decide) v hb
mask_input "9424|8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104|4809815339426005497030300474556214505035165991219677934818204933897331939334646620662990380782900913562615545856"
def inputClause9430 : CNF.NClause := [(341,true),(350,false),(354,true),(358,true),(362,true),(370,true)]
theorem inputList9430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) inputClause9430 (by decide) v hb
mask_input "9430|2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624|2414925611194539342077152617897845192926986882198097594022050812699402322767697290108799506147743167446786244608"
def inputClause9436 : CNF.NClause := [(341,true),(348,false),(355,true),(357,true),(364,true),(368,true)]
theorem inputList9436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 27) (closed_mem 7 27) inputClause9436 (by decide) v hb
mask_input "9436|573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656|639170546772530533783404874784832566493601659944620924281480228271040964418931396551739221290909693877749284864"
def inputClause9441 : CNF.NClause := [(341,true),(349,true),(352,false),(360,true),(363,true),(369,true)]
theorem inputList9441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) inputClause9441 (by decide) v hb
mask_input "9441|9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496|1223591836853964591121783617452576803443089562507020231248359534762678797473732785647313103929496035885695631360"
def inputClause9444 : CNF.NClause := [(341,true),(347,true),(353,true),(359,true),(365,true),(367,false)]
theorem inputList9444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) inputClause9444 (by decide) v hb
mask_input "9444|300613450595050653169853516389035139504087366260264943450533244356122755214669880763353471793250393988087676928|76346273095893983593048378430312343982992211173348382551416394284095013992176735711957677110003989162955374592"
def inputClause9445 : CNF.NClause := [(341,true),(347,true),(353,true),(359,true),(365,false),(367,true)]
theorem inputList9445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) inputClause9445 (by decide) v hb
mask_input "9445|75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232|301806361042181973470438515722088698611057735868547090139316327551187080403179146284472780954941784654021132288"
def inputClause9447 : CNF.NClause := [(341,true),(347,true),(353,false),(359,true),(365,true),(367,true)]
theorem inputList9447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) inputClause9447 (by decide) v hb
mask_input "9447|18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992|376941375702016716190809008252185066791553204913699979752959737929502673823837908596846588754829502145550614528"
def inputClause9453 : CNF.NClause := [(341,true),(346,true),(351,false),(356,true),(361,true),(366,true)]
theorem inputList9453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) inputClause9453 (by decide) v hb
mask_input "9453|4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248|155150742197649341352526708716586094888328384415858698945469713206127222331897318186943010218708338370116845568"
def inputClause9454 : CNF.NClause := [(341,true),(346,false),(351,true),(356,true),(361,true),(366,true)]
theorem inputList9454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) inputClause9454 (by decide) v hb
mask_input "9454|143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664|155155185851217822116080454682070742681776177760525212490146954784503534494969739626258645879654989238634545152"
def inputClause9644 : CNF.NClause := [(428,true),(429,true),(430,true),(431,false),(432,true),(433,true)]
theorem inputList9644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) inputClause9644 (by decide) v hb
mask_input "9644|5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648|38124208294161204319203195031967400922251009786417477908594094233451042982327352316799648083931919198839129150719299112648394670080"
def inputClause9664 : CNF.NClause := [(406,true),(411,false),(416,true),(421,true),(426,true),(428,true)]
theorem inputList9664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 3) (closed_mem 9 3) inputClause9664 (by decide) v hb
mask_input "9664|5288447750321988791615322464262168318627237463714249754277190362195246329890490766601513683517722278780729696200186866434048|872044045501086861344349951045801515261116905917795668551596403126746157415070174527359656654640942810648415882429019783348355072"
def inputClause9676 : CNF.NClause := [(423,true),(424,false),(425,true),(426,true),(427,true),(433,true)]
theorem inputList9676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 5) (closed_mem 9 5) inputClause9676 (by decide) v hb
mask_input "9676|43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216|22809540530540765993250547936739587029051314377896366044175898424899970602494717039539789450216085747941819883924671571374295220224"
def inputClause9693 : CNF.NClause := [(406,true),(409,true),(417,false),(420,true),(423,true),(431,true)]
theorem inputList9693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 8) (closed_mem 9 8) inputClause9693 (by decide) v hb
mask_input "9693|338460656020607282663380637712778772392143197677711984273740183180495765112991409062496875745134225841966700556811959451779072|5569710042851043221567939416010930552219948074894965082841411844878027678112416909232976693937652309814794931443124661041032593408"
def inputClause9701 : CNF.NClause := [(404,false),(410,true),(416,true),(422,true),(423,true),(429,true)]
theorem inputList9701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 9) (closed_mem 9 9) inputClause9701 (by decide) v hb
mask_input "9701|41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016|1418998944590271193560619131272057134338219669882539351192532856579409592859381427739901452318317000703584782449282240095016976384"
def inputClause9707 : CNF.NClause := [(413,false),(414,true),(415,true),(416,true),(417,true),(433,true)]
theorem inputList9707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 10) (closed_mem 9 10) inputClause9707 (by decide) v hb
mask_input "9707|21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192|22181992166696557515282307311840381087689731871502178311334349907760433892004591843211787430475138751452583375254772597055765348352"
def inputClause9711 : CNF.NClause := [(407,true),(410,true),(413,false),(421,true),(424,true),(431,true)]
theorem inputList9711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 11) (closed_mem 9 11) inputClause9711 (by decide) v hb
mask_input "9711|21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192|5594080697460456723979050463735693697567021999038297015341864528526812740613582572386004575667025463434807440963442178424116871168"
def inputClause9717 : CNF.NClause := [(405,true),(409,true),(413,false),(422,true),(426,true),(432,true)]
theorem inputList9717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) inputClause9717 (by decide) v hb
mask_input "9717|21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192|11274802778102403479360808576308116035565533836399892919224423961987364885556276195851505803348983515642575030079845546432300843008"
def inputClause9719 : CNF.NClause := [(405,false),(409,true),(413,true),(422,true),(426,true),(432,true)]
theorem inputList9719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 12) (closed_mem 9 12) inputClause9719 (by decide) v hb
mask_input "9719|82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032|11274823849261408668534900168608559580142428366799162405688288660167714257240871853275653981255066281567279547049728844051846791168"
def inputClause9731 : CNF.NClause := [(404,false),(411,true),(413,true),(420,true),(427,true),(430,true)]
theorem inputList9731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 14) (closed_mem 9 14) inputClause9731 (by decide) v hb
mask_input "9731|41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016|3121987533372833185230981078874992707386721991566533914189750835608703913633882209646304189441535687777694749584514514917542330368"
def inputClause9743 : CNF.NClause := [(407,false),(409,true),(416,true),(418,true),(425,true),(430,true)]
theorem inputList9743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 16) (closed_mem 9 16) inputClause9743 (by decide) v hb
mask_input "9743|330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128|2860163095814079422644095982822453081641885748784871051667679987264370011898916374905321498862677654908109298237763513393975656448"
def inputClause9753 : CNF.NClause := [(406,true),(410,true),(414,false),(418,true),(427,true),(432,true)]
theorem inputList9753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 18) (closed_mem 9 18) inputClause9753 (by decide) v hb
mask_input "9753|42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384|11437942219048269868882830816505704973497006493040501394741957710159053802453044432181239175985210396893383280879554464062694752256"
def inputClause9760 : CNF.NClause := [(404,true),(412,false),(415,true),(418,true),(426,true),(431,true)]
theorem inputList9760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 19) (closed_mem 9 19) inputClause9760 (by decide) v hb
mask_input "9760|10576895500643977583230644928524336637254474927428499508554380724390492659780981533203027367035444557561459392400373732868096|5719392821916225063657009295724670642623723779432689223521306255720362267470969030459796944634540084316219100658598445369985597440"
end Percolation.MaskChain
