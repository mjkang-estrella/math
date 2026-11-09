import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8976 : CNF.NClause := [(282,true),(288,true),(289,true),(295,true),(301,true),(305,false)]
theorem inputList8976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) inputClause8976 (by decide) v hb
mask_input "8976|65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032|4139229067314223125575530129173617146231723112713681260815066686931405449252456105395617792"
def inputClause8977 : CNF.NClause := [(282,true),(288,true),(289,true),(295,true),(301,false),(305,true)]
theorem inputList8977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) inputClause8977 (by decide) v hb
mask_input "8977|4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752|65250308357348805713628900781454961977775774922691768779899280167562844442152557290897539072"
def inputClause8978 : CNF.NClause := [(282,true),(288,true),(289,true),(295,false),(301,true),(305,true)]
theorem inputList8978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) inputClause8978 (by decide) v hb
mask_input "8978|63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168|69260722935757325195969903230510925232345853322721580773339181677229282626061626431196102656"
def inputClause8980 : CNF.NClause := [(282,true),(288,false),(289,true),(295,true),(301,true),(305,true)]
theorem inputList8980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) inputClause8980 (by decide) v hb
mask_input "8980|497323236409786642155382248146820840100456150797347717440463976893159497012533375533056|69323882986781368099523636776025571479038611253872843933454120602294713882182218169888800768"
def inputClause8983 : CNF.NClause := [(280,true),(287,true),(289,true),(296,true),(303,false),(306,true)]
theorem inputList8983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) inputClause8983 (by decide) v hb
mask_input "8983|16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008|130498862484687931593906761288808062317978851752007873477810869948519694653735574278521225216"
def inputClause8984 : CNF.NClause := [(280,true),(287,true),(289,true),(296,false),(303,true),(306,true)]
theorem inputList8984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) inputClause8984 (by decide) v hb
mask_input "8984|127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336|146667835546842914903662548940557501471324882126731242467235234765270096220607059383851941888"
def inputClause8987 : CNF.NClause := [(280,false),(287,true),(289,true),(296,true),(303,true),(306,true)]
theorem inputList8987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) inputClause8987 (by decide) v hb
mask_input "8987|1942668892225729070919461906823518906642406839052139521251812409738904285205208498176|146795148352694928058325255876621180782871692258928524430760472291542335312937982722779906048"
def inputClause8989 : CNF.NClause := [(294,true),(295,true),(296,true),(297,true),(298,false),(309,true)]
theorem inputList8989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) inputClause8989 (by decide) v hb
mask_input "8989|509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344|1043439850190210271345913359423822566464848255461724814134446755487260658595960425606411190272"
def inputClause8991 : CNF.NClause := [(294,true),(295,true),(296,false),(297,true),(298,true),(309,true)]
theorem inputList8991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) inputClause8991 (by decide) v hb
mask_input "8991|127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336|1043821794435772987487088692990399324870045405785537177181441031821514605089666051238820577280"
def inputClause8992 : CNF.NClause := [(294,true),(295,false),(296,true),(297,true),(298,true),(309,true)]
theorem inputList8992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) inputClause8992 (by decide) v hb
mask_input "8992|63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168|1043885451810033440177284581918162117937578264172839237689273411210556929505283655510888808448"
def inputClause8996 : CNF.NClause := [(283,true),(285,true),(292,true),(294,false),(301,true),(306,true)]
theorem inputList8996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) inputClause8996 (by decide) v hb
mask_input "8996|31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584|134452409316614327309154738329465580703594786976638112191045167153515845892503831350452682752"
def inputClause8997 : CNF.NClause := [(283,true),(285,true),(292,false),(294,true),(301,true),(306,true)]
theorem inputList8997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) inputClause8997 (by decide) v hb
mask_input "8997|7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896|134476280831961997067978196677376628103919608871876384881482309424406717548360432952478269440"
def inputClause8998 : CNF.NClause := [(283,true),(285,false),(292,true),(294,true),(301,true),(306,true)]
theorem inputList8998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) inputClause8998 (by decide) v hb
mask_input "8998|62165404551223330269422781018352605012557018849668464680057997111644937126566671941632|134484175838340002430922413370565958884756203613270292776496676790039896455375506919814856704"
def inputClause9007 : CNF.NClause := [(282,true),(286,true),(290,true),(294,true),(303,false),(308,true)]
theorem inputList9007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 18) (closed_mem 5 18) inputClause9007 (by decide) v hb
mask_input "9007|16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008|521515160023188974925965484749084457045588391480398955353125351708394209830702443006663852032"
def inputClause9008 : CNF.NClause := [(282,true),(286,true),(290,true),(294,false),(303,true),(308,true)]
theorem inputList9008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 18) (closed_mem 5 18) inputClause9008 (by decide) v hb
mask_input "9008|31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584|537779619146734637271015105792478085800233709436075415104298285608708098021000334520096915456"
def inputClause9011 : CNF.NClause := [(282,false),(286,true),(290,true),(294,true),(303,true),(308,true)]
theorem inputList9011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 18) (closed_mem 5 18) inputClause9011 (by decide) v hb
mask_input "9011|7770675568902916283677847627294075626569627356208558085007249638955617140820833992704|537811440063189294713196766578511855039924512060099089149656390295979621273191995835297038336"
def inputClause9014 : CNF.NClause := [(280,true),(288,true),(291,true),(294,false),(302,true),(307,true)]
theorem inputList9014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 19) (closed_mem 5 19) inputClause9014 (by decide) v hb
mask_input "9014|31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584|268893226727948743692943300229733145469873638711667600265567024742382779743137843221796749312"
def inputClause9016 : CNF.NClause := [(280,true),(288,false),(291,true),(294,true),(302,true),(307,true)]
theorem inputList9016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 19) (closed_mem 5 19) inputClause9016 (by decide) v hb
mask_input "9016|497323236409786642155382248146820840100456150797347717440463976893159497012533375533056|268924558091842560251399089311366395182799967449167833171765773972927048791449632824455331840"
def inputClause9028 : CNF.NClause := [(283,true),(284,false),(290,true),(296,true),(302,true),(305,true)]
theorem inputList9028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 21) (closed_mem 5 21) inputClause9028 (by decide) v hb
mask_input "9028|31082702275611665134711390509176302506278509424834232340028998555822468563283335970816|73462614730859181438457011522951041804430233910435727846551746825249226171937661741908885504"
def inputClause9040 : CNF.NClause := [(282,true),(284,false),(291,true),(298,true),(300,true),(306,true)]
theorem inputList9040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 23) (closed_mem 5 23) inputClause9040 (by decide) v hb
mask_input "9040|31082702275611665134711390509176302506278509424834232340028998555822468563283335970816|132920583812392064325069607904544726869404742905536075344305773039438164041150961166304935936"
def inputClause9049 : CNF.NClause := [(279,true),(280,true),(281,true),(282,true),(283,false),(309,true)]
theorem inputList9049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) inputClause9049 (by decide) v hb
mask_input "9049|15541351137805832567355695254588151253139254712417116170014499277911234281641667985408|1042962434453273567862412224361565919634743617375010653216750319458036298520610532604963192832"
def inputClause9055 : CNF.NClause := [(279,true),(288,true),(292,true),(296,true),(300,false),(308,true)]
theorem inputList9055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) inputClause9055 (by decide) v hb
mask_input "9055|2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376|521616980156502755950895051046275844730282786628850775615782962326319650151550760997074501632"
def inputClause9057 : CNF.NClause := [(279,true),(288,true),(292,false),(296,true),(300,true),(308,true)]
theorem inputList9057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) inputClause9057 (by decide) v hb
mask_input "9057|7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896|523646058961054685450889010618714873757892647724103954302940055352043740899361897169249370112"
def inputClause9058 : CNF.NClause := [(279,true),(288,false),(292,true),(296,true),(300,true),(308,true)]
theorem inputList9058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) inputClause9058 (by decide) v hb
mask_input "9058|497323236409786642155382248146820840100456150797347717440463976893159497012533375533056|523653518809600832250521341352437076070494154566365914518701662311697138291817085169882365952"
def inputClause9060 : CNF.NClause := [(279,true),(286,true),(293,true),(295,true),(302,true),(306,false)]
theorem inputList9060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) inputClause9060 (by decide) v hb
mask_input "9060|130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064|8227840925307058767343718218633994095591424994032439500334156775620858877901747900767010816"
def inputClause9061 : CNF.NClause := [(279,true),(286,true),(293,true),(295,true),(302,false),(306,true)]
theorem inputList9061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) inputClause9061 (by decide) v hb
mask_input "9061|8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504|130449999505376223943450459523196683758679528613988614538502583736883736863701950271770853376"
def inputClause9062 : CNF.NClause := [(279,true),(286,true),(293,true),(295,false),(302,true),(306,true)]
theorem inputList9062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) inputClause9062 (by decide) v hb
mask_input "9062|63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168|138534486036453715598328353349071403335352543801350299033214766145258937647137692824436211712"
def inputClause9063 : CNF.NClause := [(279,true),(286,true),(293,false),(295,true),(302,true),(306,true)]
theorem inputList9063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) inputClause9063 (by decide) v hb
mask_input "9063|15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792|138582229067149055115975270044893498136002187591826844414089050687040680958850896028487385088"
def inputClause9064 : CNF.NClause := [(279,true),(286,false),(293,true),(295,true),(302,true),(306,true)]
theorem inputList9064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) inputClause9064 (by decide) v hb
mask_input "9064|124330809102446660538845562036705210025114037699336929360115994223289874253133343883264|138598019079905065841863703431272159697675377074614660204117785418307038772881043963160559616"
def inputClause9067 : CNF.NClause := [(279,true),(287,true),(290,true),(298,true),(301,false),(307,true)]
theorem inputList9067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) inputClause9067 (by decide) v hb
mask_input "9067|4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752|261252102890796130716682394218350363260390726861538331734883255343501625781836631570814861312"
def inputClause9068 : CNF.NClause := [(279,true),(287,true),(290,true),(298,false),(301,true),(307,true)]
theorem inputList9068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) inputClause9068 (by decide) v hb
mask_input "9068|509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344|264816915849381481367652174173066775042230796550453720173496501129871793056422470806635806720"
def inputClause9069 : CNF.NClause := [(279,true),(287,true),(290,false),(298,true),(301,true),(307,true)]
theorem inputList9069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) inputClause9069 (by decide) v hb
mask_input "9069|1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224|265324185550519463742650664066176532299133261824267014845285774386302815743375254849679523840"
def inputClause9070 : CNF.NClause := [(279,true),(287,false),(290,true),(298,true),(301,true),(307,true)]
theorem inputList9070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) inputClause9070 (by decide) v hb
mask_input "9070|248661618204893321077691124073410420050228075398673858720231988446579748506266687766528|265325926181846897995898207904045046172073613420794805562296816010221941801614798716493889536"
def inputClause9072 : CNF.NClause := [(279,true),(285,true),(291,true),(297,true),(303,true),(305,false)]
theorem inputList9072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) inputClause9072 (by decide) v hb
mask_input "9072|65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032|16554959030347975080263169158823343889628450225964380012692605546722809850942480174020558848"
def inputClause9073 : CNF.NClause := [(279,true),(285,true),(291,true),(297,true),(303,false),(305,true)]
theorem inputList9073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) inputClause9073 (by decide) v hb
mask_input "9073|16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008|65443822462375641150705865680648419754863691673946850027959976331227961045262561122422095872"
def inputClause9092 : CNF.NClause := [(314,true),(319,true),(324,true),(329,false),(334,true),(335,true)]
theorem inputList9092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) inputClause9092 (by decide) v hb
mask_input "9092|1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912|105023311950474703650459662182011782046094867974751243541840645716731932809228640206312605480323645440"
def inputClause9097 : CNF.NClause := [(312,true),(317,true),(322,true),(327,true),(332,false),(335,true)]
theorem inputList9097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) inputClause9097 (by decide) v hb
mask_input "9097|8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296|70274248823876790890611522866245075489256251790413711168528794883183287311194600506451354057669869568"
def inputClause9122 : CNF.NClause := [(314,true),(318,true),(322,true),(326,false),(330,true),(339,true)]
theorem inputList9122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 6) (closed_mem 6 6) inputClause9122 (by decide) v hb
mask_input "9122|136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864|1122068733133385217335163858775805139921914770209696157483392126437664255245297631658508451510478700544"
def inputClause9127 : CNF.NClause := [(312,true),(319,true),(321,true),(328,true),(330,false),(337,true)]
theorem inputList9127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) inputClause9127 (by decide) v hb
mask_input "9127|2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824|280520253764710440642034407537653903711643433940174927059204830481727308252180217585417770885619646464"
def inputClause9142 : CNF.NClause := [(311,true),(317,false),(323,true),(329,true),(330,true),(336,true)]
theorem inputList9142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) inputClause9142 (by decide) v hb
mask_input "9142|266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072|143282014541424327860085560727630325709955893193091538035884992355530139483138270010853871055303344128"
end Percolation.MaskChain
