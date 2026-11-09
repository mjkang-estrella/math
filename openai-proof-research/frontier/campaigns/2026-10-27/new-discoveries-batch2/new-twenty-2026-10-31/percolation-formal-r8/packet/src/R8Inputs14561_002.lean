import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8912 : CNF.NClause := [(281,true),(286,true),(291,true),(296,false),(301,true),(304,true)]
theorem inputList8912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) inputClause8912 (by decide) v hb
mask_input "8912|127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336|36670754376058914744087946133839831817895073134044608734398454419813051439398984522066296832"
def inputClause8917 : CNF.NClause := [(282,true),(287,true),(292,true),(297,true),(302,false),(304,true)]
theorem inputList8917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 3) (closed_mem 5 3) inputClause8917 (by decide) v hb
mask_input "8917|8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504|32855418722469918523590534210543272684892211943978734487403617408707774546001652008737570816"
def inputClause8924 : CNF.NClause := [(280,true),(285,true),(290,true),(295,false),(300,true),(304,true)]
theorem inputList8924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) inputClause8924 (by decide) v hb
mask_input "8924|63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168|34631664998705346062191538574194941197359283716349794372288350804741576117806185910500327424"
def inputClause8926 : CNF.NClause := [(280,true),(285,false),(290,true),(295,true),(300,true),(304,true)]
theorem inputList8926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) inputClause8926 (by decide) v hb
mask_input "8926|62165404551223330269422781018352605012557018849668464680057997111644937126566671941632|34695260207561247529057158079176715912287129546633005211656050135786788888486663615896616960"
def inputClause8927 : CNF.NClause := [(280,false),(285,true),(290,true),(295,true),(300,true),(304,true)]
theorem inputList8927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) inputClause8927 (by decide) v hb
mask_input "8927|1942668892225729070919461906823518906642406839052139521251812409738904285205208498176|34695320430296906526658356582495827441373235461245015827981208941971490794519504977360060416"
def inputClause8933 : CNF.NClause := [(299,false),(300,true),(301,true),(302,true),(303,true),(309,true)]
theorem inputList8933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 5) (closed_mem 5 5) inputClause8933 (by decide) v hb
mask_input "8933|1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688|1073517959528274167463470877791742290874123843461948404085246016809758944975278444158650417152"
def inputClause8941 : CNF.NClause := [(281,true),(288,true),(290,true),(297,true),(299,false),(306,true)]
theorem inputList8941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) inputClause8941 (by decide) v hb
mask_input "8941|1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688|130627422483968753666632998519415922328663726309395826914908751138358986122617599361305018368"
def inputClause8961 : CNF.NClause := [(289,true),(290,true),(291,false),(292,true),(293,true),(309,true)]
theorem inputList8961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) inputClause8961 (by decide) v hb
mask_input "8961|3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448|1042989275338023004648120583107001546783717242189102417102445695124195456091667070368178241536"
def inputClause8963 : CNF.NClause := [(289,false),(290,true),(291,true),(292,true),(293,true),(309,true)]
theorem inputList8963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) inputClause8963 (by decide) v hb
mask_input "8963|994646472819573284310764496293641680200912301594695434880927953786318994025066751066112|1042992259277441463367973515400490427708757844926007201188750337908056815048649145568431439872"
def inputClause8964 : CNF.NClause := [(283,true),(286,true),(289,true),(297,true),(300,true),(307,false)]
theorem inputList8964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) inputClause8964 (by decide) v hb
mask_input "8964|260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128|2292799992009356672829418365214135366224381108468184731446069063970966482336313636219256832"
def inputClause8971 : CNF.NClause := [(281,true),(285,true),(289,true),(298,true),(302,false),(308,true)]
theorem inputList8971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) inputClause8971 (by decide) v hb
mask_input "8971|8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504|521991529632927214854361929681104279410761802631030286693689593636635925506094753003335581696"
def inputClause8979 : CNF.NClause := [(282,true),(288,true),(289,false),(295,true),(301,true),(305,true)]
theorem inputList8979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) inputClause8979 (by decide) v hb
mask_input "8979|994646472819573284310764496293641680200912301594695434880927953786318994025066751066112|69323385663544958312881481393777424658198510797722046585736680138317820722685205636513267712"
def inputClause8981 : CNF.NClause := [(282,false),(288,true),(289,true),(295,true),(301,true),(305,true)]
theorem inputList8981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) inputClause8981 (by decide) v hb
mask_input "8981|7770675568902916283677847627294075626569627356208558085007249638955617140820833992704|69324372539342208983249508480426091005803085140396285072613476059021968086062089882430341120"
def inputClause8982 : CNF.NClause := [(280,true),(287,true),(289,true),(296,true),(303,true),(306,false)]
theorem inputList8982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) inputClause8982 (by decide) v hb
mask_input "8982|130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064|16424847809956710762873802737882885299096621706715443442187004784674341866988718732250972160"
def inputClause8990 : CNF.NClause := [(294,true),(295,true),(296,true),(297,false),(298,true),(309,true)]
theorem inputList8990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) inputClause8990 (by decide) v hb
mask_input "8990|254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672|1043694479687252082106696915134873738734979689010933056165776273043429956258430842694684114944"
def inputClause8993 : CNF.NClause := [(294,false),(295,true),(296,true),(297,true),(298,true),(309,true)]
theorem inputList8993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) inputClause8993 (by decide) v hb
mask_input "8993|31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584|1043917280497163666522382526382043514471344693366490267943189600905078091713092457646922924032"
def inputClause8995 : CNF.NClause := [(283,true),(285,true),(292,true),(294,true),(301,false),(306,true)]
theorem inputList8995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) inputClause8995 (by decide) v hb
mask_input "8995|4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752|130410166051075581481715791416528220915258279382957269943689075949328245500785960074120003584"
def inputClause9002 : CNF.NClause := [(281,true),(287,true),(293,true),(294,false),(300,true),(305,true)]
theorem inputList9002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 17) (closed_mem 5 17) inputClause9002 (by decide) v hb
mask_input "9002|31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584|67238354109559143364186899479498064639039535100690488176088492411568430053651589049173934080"
def inputClause9005 : CNF.NClause := [(281,false),(287,true),(293,true),(294,true),(300,true),(305,true)]
theorem inputList9005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 17) (closed_mem 5 17) inputClause9005 (by decide) v hb
mask_input "9005|3885337784451458141838923813647037813284813678104279042503624819477808570410416996352|67270178911351585257826702104455647525768151009527840325725639602464772783651820774791053312"
def inputClause9012 : CNF.NClause := [(280,true),(288,true),(291,true),(294,true),(302,true),(307,false)]
theorem inputList9012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 19) (closed_mem 5 19) inputClause9012 (by decide) v hb
mask_input "9012|260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128|8184450444264750995680196577214137389052113516078790438057236919543135581239546966356000768"
def inputClause9023 : CNF.NClause := [(284,false),(285,true),(286,true),(287,true),(288,true),(309,true)]
theorem inputList9023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 20) (closed_mem 5 20) inputClause9023 (by decide) v hb
mask_input "9023|31082702275611665134711390509176302506278509424834232340028998555822468563283335970816|1042963352364325144519398233807316893747427005912242105352674110939399900152885292065978580992"
def inputClause9034 : CNF.NClause := [(281,true),(284,false),(292,true),(295,true),(303,true),(307,true)]
theorem inputList9034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 22) (closed_mem 5 22) inputClause9034 (by decide) v hb
mask_input "9034|31082702275611665134711390509176302506278509424834232340028998555822468563283335970816|277108511212870901460437130506332385751011980509095826262105570428493291213192167257435799552"
def inputClause9046 : CNF.NClause := [(280,true),(284,false),(293,true),(297,true),(301,true),(308,true)]
theorem inputList9046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 24) (closed_mem 5 24) inputClause9046 (by decide) v hb
mask_input "9046|31082702275611665134711390509176302506278509424834232340028998555822468563283335970816|525825827677573226416320586472073342911812400354252148874551369588672663844219973556815003648"
def inputClause9050 : CNF.NClause := [(279,true),(280,true),(281,true),(282,false),(283,true),(309,true)]
theorem inputList9050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) inputClause9050 (by decide) v hb
mask_input "9050|7770675568902916283677847627294075626569627356208558085007249638955617140820833992704|1042962442223949136765328508039413546928819243944638009425308404465285937476227673425797185536"
def inputClause9051 : CNF.NClause := [(279,true),(280,true),(281,false),(282,true),(283,true),(309,true)]
theorem inputList9051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) inputClause9051 (by decide) v hb
mask_input "9051|3885337784451458141838923813647037813284813678104279042503624819477808570410416996352|1042962446109286921216786649878337360575857057229451687529587446968910756954036243836214181888"
def inputClause9052 : CNF.NClause := [(279,true),(280,false),(281,true),(282,true),(283,true),(309,true)]
theorem inputList9052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) inputClause9052 (by decide) v hb
mask_input "9052|1942668892225729070919461906823518906642406839052139521251812409738904285205208498176|1042962448051955813442515720797799267399375963871858526581726968220723166692940529041422680064"
def inputClause9056 : CNF.NClause := [(279,true),(288,true),(292,true),(296,false),(300,true),(308,true)]
theorem inputList9056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) inputClause9056 (by decide) v hb
mask_input "9056|127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336|523526701384316336656771718879159636756268538247912590850754343997589382620078889159121436672"
def inputClause9074 : CNF.NClause := [(279,true),(285,true),(291,true),(297,false),(303,true),(305,true)]
theorem inputList9074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) inputClause9074 (by decide) v hb
mask_input "9074|254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672|81485480776009719080069875476872272773144005274066098001719582369893713780898837683616350208"
def inputClause9076 : CNF.NClause := [(279,true),(285,false),(291,true),(297,true),(303,true),(305,true)]
theorem inputList9076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) inputClause9076 (by decide) v hb
mask_input "9076|62165404551223330269422781018352605012557018849668464680057997111644937126566671941632|81740048107646978617523161765142426690670426266255490364584419868065899798432128205217333248"
def inputClause9082 : CNF.NClause := [(279,true),(284,false),(289,true),(294,true),(299,true),(304,true)]
theorem inputList9082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 30) (closed_mem 5 30) inputClause9082 (by decide) v hb
mask_input "9082|31082702275611665134711390509176302506278509424834232340028998555822468563283335970816|33643917914456512454676144546863383244555311922643992610917148662728444842350025457415487488"
def inputClause9100 : CNF.NClause := [(312,true),(317,false),(322,true),(327,true),(332,true),(335,true)]
theorem inputList9100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) inputClause9100 (by decide) v hb
mask_input "9100|266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072|79022984724629348474341232397002289756654604175921266332635633928622121530526381619276653895501217792"
def inputClause9103 : CNF.NClause := [(313,true),(318,true),(323,true),(328,true),(333,false),(335,true)]
theorem inputList9103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) inputClause9103 (by decide) v hb
mask_input "9103|17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592|70556474454697200201302974464726267287211081792244624371432930361248078648009171469750286450602016768"
def inputClause9107 : CNF.NClause := [(313,false),(318,true),(323,true),(328,true),(333,true),(335,true)]
theorem inputList9107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) inputClause9107 (by decide) v hb
mask_input "9107|16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192|88054463565562577464172973570560158760410541905761242951489330001265141530512571194284094812395143168"
def inputClause9112 : CNF.NClause := [(311,true),(316,false),(321,true),(326,true),(331,true),(335,true)]
theorem inputList9112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 4) (closed_mem 6 4) inputClause9112 (by decide) v hb
mask_input "9112|133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536|74507503958842865027130651832383086723978012982252032149130146666870308752453205581214537780119470080"
def inputClause9116 : CNF.NClause := [(330,true),(331,true),(332,true),(333,false),(334,true),(340,true)]
theorem inputList9116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) inputClause9116 (by decide) v hb
mask_input "9116|17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592|2290051508847813484818009831792149569524768394145193420937781824911220790161746591615018296343137353728"
def inputClause9118 : CNF.NClause := [(330,true),(331,false),(332,true),(333,true),(334,true),(340,true)]
theorem inputList9118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) inputClause9118 (by decide) v hb
mask_input "9118|4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648|2303175013196511556364244845154855297716887410730552695556336448549680508156942847154359375405275676672"
def inputClause9121 : CNF.NClause := [(314,true),(318,true),(322,true),(326,true),(330,false),(339,true)]
theorem inputList9121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 6) (closed_mem 6 6) inputClause9121 (by decide) v hb
mask_input "9121|2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824|1120018185578901143656064637937882369891896173868233770824242966494154924308548216730486407907019587584"
def inputClause9129 : CNF.NClause := [(312,true),(319,true),(321,false),(328,true),(330,true),(337,true)]
theorem inputList9129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) inputClause9129 (by decide) v hb
mask_input "9129|4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152|282703232515421610746242119721359185972767397962023426190090707004921616811928032227541238138468827136"
def inputClause9138 : CNF.NClause := [(311,true),(317,true),(323,true),(329,true),(330,true),(336,false)]
theorem inputList9138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) inputClause9138 (by decide) v hb
mask_input "9138|139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736|3298235153691054814005717569815829521367374953991236686231916925494125311843933504617780596088766464"
def inputClause9139 : CNF.NClause := [(311,true),(317,true),(323,true),(329,true),(330,false),(336,true)]
theorem inputList9139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause9139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) inputClause9139 (by decide) v hb
mask_input "9139|2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824|141095030815020806049473357878225975538617049100263620181055465129321164261404616667699110748541157376"
end Percolation.MaskChain
