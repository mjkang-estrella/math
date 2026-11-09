import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8905 : CNF.NClause := [(283,true),(288,true),(293,true),(298,true),(303,false),(304,true)]
theorem inputList8905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) inputClause8905 (by decide) v hb
mask_input "8905|16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008|33118261823588059666885937406536494792960929589302488964628987627745448295789916718540783616"
def inputClause8906 : CNF.NClause := [(283,true),(288,true),(293,true),(298,false),(303,true),(304,true)]
theorem inputList8906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) inputClause8906 (by decide) v hb
mask_input "8906|509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344|48905290640180326835466391491709175541109809640213494907059076110241903368955776191462113280"
def inputClause8907 : CNF.NClause := [(283,true),(288,true),(293,false),(298,true),(303,true),(304,true)]
theorem inputList8907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) inputClause8907 (by decide) v hb
mask_input "8907|15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792|49398635290698835184484530681870821814489462141804463842760016375319917589992209299990904832"
def inputClause8908 : CNF.NClause := [(283,true),(288,false),(293,true),(298,true),(303,true),(304,true)]
theorem inputList8908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) inputClause8908 (by decide) v hb
mask_input "8908|497323236409786642155382248146820840100456150797347717440463976893159497012533375533056|49414052311027538570391347531563373260532576282479181622000670758603605534399597834632429568"
def inputClause8911 : CNF.NClause := [(281,true),(286,true),(291,true),(296,true),(301,false),(304,true)]
theorem inputList8911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) inputClause8911 (by decide) v hb
mask_input "8911|4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752|32723997171910847951942832612546661630857853121316857248790932299188937671107519653835964416"
def inputClause8913 : CNF.NClause := [(281,true),(286,true),(291,false),(296,true),(301,true),(304,true)]
theorem inputList8913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) inputClause8913 (by decide) v hb
mask_input "8913|3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448|36794090538688541831342480931380243386239986259442350968323689486082554994658092799198494720"
def inputClause8914 : CNF.NClause := [(281,true),(286,false),(291,true),(296,true),(301,true),(304,true)]
theorem inputList8914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) inputClause8914 (by decide) v hb
mask_input "8914|124330809102446660538845562036705210025114037699336929360115994223289874253133343883264|36797944793770717677819185143803381247750764794611030413133853081903476980759939932858875904"
def inputClause8915 : CNF.NClause := [(281,false),(286,true),(291,true),(296,true),(301,true),(304,true)]
theorem inputList8915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) inputClause8915 (by decide) v hb
mask_input "8915|3885337784451458141838923813647037813284813678104279042503624819477808570410416996352|36798065239242035673021582150441604305922976623835051645784170694272880792825622655785762816"
def inputClause8921 : CNF.NClause := [(282,false),(287,true),(292,true),(297,true),(302,true),(304,true)]
theorem inputList8921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 3) (closed_mem 5 3) inputClause8921 (by decide) v hb
mask_input "8921|7770675568902916283677847627294075626569627356208558085007249638955617140820833992704|41003554857132293965748033286333158035022458949015123281390094198875660789437858012637167616"
def inputClause8923 : CNF.NClause := [(280,true),(285,true),(290,true),(295,true),(300,false),(304,true)]
theorem inputList8923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) inputClause8923 (by decide) v hb
mask_input "8923|2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376|32658286396631312666118981813548356103840673709985918629484589744429519233660453476385161216"
def inputClause8925 : CNF.NClause := [(280,true),(285,true),(290,false),(295,true),(300,true),(304,true)]
theorem inputList8925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) inputClause8925 (by decide) v hb
mask_input "8925|1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224|34693333080020159605818805972965146981531740279048665489250968337876327895435740049066426368"
def inputClause8929 : CNF.NClause := [(299,true),(300,true),(301,true),(302,true),(303,false),(309,true)]
theorem inputList8929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 5) (closed_mem 5 5) inputClause8929 (by decide) v hb
mask_input "8929|16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008|1058240189705765521816457535128671954666237830509453882205474963439601085227053418862274936832"
def inputClause8932 : CNF.NClause := [(299,true),(300,false),(301,true),(302,true),(303,true),(309,true)]
theorem inputList8932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 5) (closed_mem 5 5) inputClause8932 (by decide) v hb
mask_input "8932|2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376|1072499441540106924420336654947537601793598109265115435959927946585081754325396775805558718464"
def inputClause8934 : CNF.NClause := [(283,true),(287,true),(291,true),(295,true),(299,true),(308,false)]
theorem inputList8934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) inputClause8934 (by decide) v hb
mask_input "8934|521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728256|1086418151288316725620999876771984713350699600671518505864863572022384832458160800519946240"
def inputClause8936 : CNF.NClause := [(283,true),(287,true),(291,true),(295,false),(299,true),(308,true)]
theorem inputList8936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) inputClause8936 (by decide) v hb
mask_input "8936|63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168|522503970718656302120147207181810000874993749991849138160884439217701673156254753311401443328"
def inputClause8937 : CNF.NClause := [(283,true),(287,true),(291,false),(295,true),(299,true),(308,true)]
theorem inputList8937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) inputClause8937 (by decide) v hb
mask_input "8937|3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448|522563649507025476517205853051587619375805804729944819886977294894928852295896257316465410048"
def inputClause8938 : CNF.NClause := [(283,true),(287,false),(291,true),(295,true),(299,true),(308,true)]
theorem inputList8938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) inputClause8938 (by decide) v hb
mask_input "8938|248661618204893321077691124073410420050228075398673858720231988446579748506266687766528|522567379431298549917022018418448720532106558151075799994858098374755550992123851316781907968"
def inputClause8939 : CNF.NClause := [(283,false),(287,true),(291,true),(295,true),(299,true),(308,true)]
theorem inputList8939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) inputClause8939 (by decide) v hb
mask_input "8939|15541351137805832567355695254588151253139254712417116170014499277911234281641667985408|522567612551565617004510528753877539354375355239896486251600648592244719660638075941801689088"
def inputClause8940 : CNF.NClause := [(281,true),(288,true),(290,true),(297,true),(299,true),(306,false)]
theorem inputList8940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) inputClause8940 (by decide) v hb
mask_input "8940|130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064|1275637986728887188586697305420409101895483311608874999513832604355773587645718518659284992"
def inputClause8942 : CNF.NClause := [(281,true),(288,true),(290,true),(297,false),(299,true),(306,true)]
theorem inputList8942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) inputClause8942 (by decide) v hb
mask_input "8942|254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672|131391310975094185948983665652569439139058026957020553008897303806866879110028850626123792384"
def inputClause8943 : CNF.NClause := [(281,true),(288,true),(290,false),(297,true),(299,true),(306,true)]
theorem inputList8943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) inputClause8943 (by decide) v hb
mask_input "8943|1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224|131643951179190357563198599834628024125829058681625605649357059507128604134511217580894584832"
def inputClause8944 : CNF.NClause := [(281,true),(288,false),(290,true),(297,true),(299,true),(306,true)]
theorem inputList8944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) inputClause8944 (by decide) v hb
mask_input "8944|497323236409786642155382248146820840100456150797347717440463976893159497012533375533056|131645443148899586923125065981372464588349360050077997692509380899059283613002255181021184000"
def inputClause8945 : CNF.NClause := [(281,false),(288,true),(290,true),(297,true),(299,true),(306,true)]
theorem inputList8945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) inputClause8945 (by decide) v hb
mask_input "8945|3885337784451458141838923813647037813284813678104279042503624819477808570410416996352|131645936586798212258309079524696797762151647221415116935947778859411357294690697303979720704"
def inputClause8946 : CNF.NClause := [(282,true),(285,true),(293,true),(296,true),(299,true),(307,false)]
theorem inputList8946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) inputClause8946 (by decide) v hb
mask_input "8946|260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128|1161817016333381722321526032299619129155304694908810144963688915269171185575545352751153152"
def inputClause8948 : CNF.NClause := [(282,true),(285,true),(293,true),(296,false),(299,true),(307,true)]
theorem inputList8948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) inputClause8948 (by decide) v hb
mask_input "8948|127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336|261775107238626695384290796293174437608677542309544529210724907654545328724047435200089554944"
def inputClause8949 : CNF.NClause := [(282,true),(285,true),(293,false),(296,true),(299,true),(307,true)]
theorem inputList8949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) inputClause8949 (by decide) v hb
mask_input "8949|15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792|261886507643582487592133601916759325476860044487323135099431571585369396451378242676208959488"
def inputClause8950 : CNF.NClause := [(282,true),(285,false),(293,true),(296,true),(299,true),(307,true)]
theorem inputList8950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) inputClause8950 (by decide) v hb
mask_input "8950|62165404551223330269422781018352605012557018849668464680057997111644937126566671941632|261902359821743049541352304725919005391138246527129800557924986374632865910345517177554075648"
def inputClause8953 : CNF.NClause := [(280,true),(286,true),(292,true),(298,true),(299,false),(305,true)]
theorem inputList8953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 9) (closed_mem 5 9) inputClause8953 (by decide) v hb
mask_input "8953|1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688|65702493682047727540821469332196738356080394750583740035563458283115720498098347646975475712"
def inputClause8954 : CNF.NClause := [(280,true),(286,true),(292,true),(298,false),(299,true),(305,true)]
theorem inputList8954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 9) (closed_mem 5 9) inputClause8954 (by decide) v hb
mask_input "8954|509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344|66211752676131349062388580754299082896343261849000224098222493395454315823039181823521325056"
def inputClause8956 : CNF.NClause := [(280,true),(286,false),(292,true),(298,true),(299,true),(305,true)]
theorem inputList8956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 9) (closed_mem 5 9) inputClause8956 (by decide) v hb
mask_input "8956|124330809102446660538845562036705210025114037699336929360115994223289874253133343883264|66720887339405868137295153330839390731396103833379008823952168391798687858105762866723291136"
def inputClause8959 : CNF.NClause := [(289,true),(290,true),(291,true),(292,true),(293,false),(309,true)]
theorem inputList8959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) inputClause8959 (by decide) v hb
mask_input "8959|15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792|1042977339580349169768708853933046023083554831241483280757227123988750020263738769567165448192"
def inputClause8960 : CNF.NClause := [(289,true),(290,true),(291,true),(292,false),(293,true),(309,true)]
theorem inputList8960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) inputClause8960 (by decide) v hb
mask_input "8960|7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896|1042985296752131726354983340049016372216996438539896038320706171412380310815690970101173977088"
def inputClause8962 : CNF.NClause := [(289,true),(290,false),(291,true),(292,true),(293,true),(309,true)]
theorem inputList8962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) inputClause8962 (by decide) v hb
mask_input "8962|1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224|1042991264630968643794689204635994134067077644013705606493315456980103028729655120501680373760"
def inputClause8965 : CNF.NClause := [(283,true),(286,true),(289,true),(297,true),(300,false),(307,true)]
theorem inputList8965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) inputClause8965 (by decide) v hb
mask_input "8965|2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376|260996368986489089628922020793205161819760867104042088562235906131977391552280075321510723584"
def inputClause8967 : CNF.NClause := [(283,true),(286,true),(289,false),(297,true),(300,true),(307,true)]
theorem inputList8967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) inputClause8967 (by decide) v hb
mask_input "8967|994646472819573284310764496293641680200912301594695434880927953786318994025066751066112|263032410316350756141906155717118246339132134585406430117437165653377986533049386960943054848"
def inputClause8968 : CNF.NClause := [(283,true),(286,false),(289,true),(297,true),(300,true),(307,true)]
theorem inputList8968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) inputClause8968 (by decide) v hb
mask_input "8968|124330809102446660538845562036705210025114037699336929360115994223289874253133343883264|263033280632014473268529927636052503275602310383670325475942686465337549562169158894350237696"
def inputClause8969 : CNF.NClause := [(283,false),(286,true),(289,true),(297,true),(300,true),(307,true)]
theorem inputList8969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) inputClause8969 (by decide) v hb
mask_input "8969|15541351137805832567355695254588151253139254712417116170014499277911234281641667985408|263033389421472437909357899125919285392661082358453312395755876566832494940809130386026135552"
def inputClause8972 : CNF.NClause := [(281,true),(285,true),(289,true),(298,false),(302,true),(308,true)]
theorem inputList8972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) inputClause8972 (by decide) v hb
mask_input "8972|509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344|529630414544181537677868601012639447514704809107277547633575120321714855380207265651523321856"
def inputClause8973 : CNF.NClause := [(281,true),(285,true),(289,false),(298,true),(302,true),(308,true)]
theorem inputList8973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) inputClause8973 (by decide) v hb
mask_input "8973|994646472819573284310764496293641680200912301594695434880927953786318994025066751066112|530138678891792339626151401670245498413287475293392437000799274506099664386154074761318105088"
def inputClause8974 : CNF.NClause := [(281,true),(285,false),(289,true),(298,true),(302,true),(308,true)]
theorem inputList8974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) inputClause8974 (by decide) v hb
mask_input "8974|62165404551223330269422781018352605012557018849668464680057997111644937126566671941632|530139611372860607976105443011960773702362663648675182027769475376056339060210973261397229568"
end Percolation.MaskChain
