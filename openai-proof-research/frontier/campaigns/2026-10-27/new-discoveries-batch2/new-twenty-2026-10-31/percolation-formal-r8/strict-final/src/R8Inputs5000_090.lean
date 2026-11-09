import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14357 : CNF.NClause := [(19,true),(22,true),(735,false)]
theorem inputList14357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14357 = (containClause5 19 22) := by decide
  rw [he]
  exact input_contain 19 22 (by decide) v hb
mask_input "14357|180736893357325919804742965901096183254486650358500961579737723575212405143116703993975930943694719806137463391890175780999890999416217020648099397663164550811570949854893831716648452639533025774320471006645409943407034368|4718592"
def inputClause14358 : CNF.NClause := [(19,true),(23,true),(736,false)]
theorem inputList14358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14358
  have he : decodeClause inputClause14358 = containClause5 19 23 := by decide
  rw [he]
  exact input_contain 19 23 (by decide) v hb
mask_input "14358|361473786714651839609485931802192366508973300717001923159475447150424810286233407987951861887389439612274926783780351561999781998832434041296198795326329101623141899709787663433296905279066051548640942013290819886814068736|8912896"
def inputClause14359 : CNF.NClause := [(19,true),(24,true),(737,false)]
theorem inputList14359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14359
  have he : decodeClause inputClause14359 = containClause5 19 24 := by decide
  rw [he]
  exact input_contain 19 24 (by decide) v hb
mask_input "14359|722947573429303679218971863604384733017946601434003846318950894300849620572466815975903723774778879224549853567560703123999563997664868082592397590652658203246283799419575326866593810558132103097281884026581639773628137472|17301504"
def inputClause14361 : CNF.NClause := [(19,true),(26,true),(739,false)]
theorem inputList14361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14361 = (containClause5 19 26) := by decide
  rw [he]
  exact input_contain 19 26 (by decide) v hb
mask_input "14361|2891790293717214716875887454417538932071786405736015385275803577203398482289867263903614895099115516898199414270242812495998255990659472330369590362610632812985135197678301307466375242232528412389127536106326559094512549888|67633152"
def inputClause14362 : CNF.NClause := [(19,true),(27,true),(740,false)]
theorem inputList14362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14362
  have he : decodeClause inputClause14362 = containClause5 19 27 := by decide
  rw [he]
  exact input_contain 19 27 (by decide) v hb
mask_input "14362|5783580587434429433751774908835077864143572811472030770551607154406796964579734527807229790198231033796398828540485624991996511981318944660739180725221265625970270395356602614932750484465056824778255072212653118189025099776|134742016"
def inputClause14363 : CNF.NClause := [(19,true),(28,true),(741,false)]
theorem inputList14363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14363 = (containClause5 19 28) := by decide
  rw [he]
  exact input_contain 19 28 (by decide) v hb
mask_input "14363|11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396462067592797657080971249983993023962637889321478361450442531251940540790713205229865500968930113649556510144425306236378050199552|268959744"
def inputClause14364 : CNF.NClause := [(19,true),(29,true),(742,false)]
theorem inputList14364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14364 = (containClause5 19 29) := by decide
  rw [he]
  exact input_contain 19 29 (by decide) v hb
mask_input "14364|23134322349737717735007099635340311456574291245888123082206428617627187858318938111228919160792924135185595314161942499967986047925275778642956722900885062503881081581426410459731001937860227299113020288850612472756100399104|537395200"
def inputClause14369 : CNF.NClause := [(20,true),(3,true),(747,false)]
theorem inputList14369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14369 = (containClause5 20 3) := by decide
  rw [he]
  exact input_contain 20 3 (by decide) v hb
mask_input "14369|740298315191606967520227188330889966610377319868419938630605715764070011466206019559325413145373572325939050053182159998975553533608824916574615132828322000124194610605645134711392062011527273571616649243219599128195212771328|1048584"
def inputClause14372 : CNF.NClause := [(20,true),(6,true),(750,false)]
theorem inputList14372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14372 = (containClause5 20 6) := by decide
  rw [he]
  exact input_contain 20 6 (by decide) v hb
mask_input "14372|5922386521532855740161817506647119732883018558947359509044845726112560091729648156474603305162988578607512400425457279991804428268870599332596921062626576000993556884845161077691136496092218188572933193945756793025561702170624|1048640"
def inputClause14373 : CNF.NClause := [(20,true),(7,true),(751,false)]
theorem inputList14373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14373 = (containClause5 20 7) := by decide
  rw [he]
  exact input_contain 20 7 (by decide) v hb
mask_input "14373|11844773043065711480323635013294239465766037117894719018089691452225120183459296312949206610325977157215024800850914559983608856537741198665193842125253152001987113769690322155382272992184436377145866387891513586051123404341248|1048704"
def inputClause14375 : CNF.NClause := [(20,true),(9,true),(753,false)]
theorem inputList14375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14375 = (containClause5 20 9) := by decide
  rw [he]
  exact input_contain 20 9 (by decide) v hb
mask_input "14375|47379092172262845921294540053176957863064148471578876072358765808900480733837185251796826441303908628860099203403658239934435426150964794660775368501012608007948455078761288621529091968737745508583465551566054344204493617364992|1049088"
def inputClause14378 : CNF.NClause := [(20,true),(12,true),(756,false)]
theorem inputList14378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14378 = (containClause5 20 12) := by decide
  rw [he]
  exact input_contain 20 12 (by decide) v hb
mask_input "14378|379032737378102767370356320425415662904513187772631008578870126471203845870697482014374611530431269030880793627229265919475483409207718357286202948008100864063587640630090308972232735749901964068667724412528434753635948938919936|1052672"
def inputClause14379 : CNF.NClause := [(20,true),(13,true),(757,false)]
theorem inputList14379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14379 = (containClause5 20 13) := by decide
  rw [he]
  exact input_contain 20 13 (by decide) v hb
mask_input "14379|758065474756205534740712640850831325809026375545262017157740252942407691741394964028749223060862538061761587254458531838950966818415436714572405896016201728127175281260180617944465471499803928137335448825056869507271897877839872|1056768"
def inputClause14380 : CNF.NClause := [(20,true),(14,true),(758,false)]
theorem inputList14380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14380 = (containClause5 20 14) := by decide
  rw [he]
  exact input_contain 20 14 (by decide) v hb
mask_input "14380|1516130949512411069481425281701662651618052751090524034315480505884815383482789928057498446121725076123523174508917063677901933636830873429144811792032403456254350562520361235888930942999607856274670897650113739014543795755679744|1064960"
def inputClause14381 : CNF.NClause := [(20,true),(15,true),(759,false)]
theorem inputList14381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14381 = (containClause5 20 15) := by decide
  rw [he]
  exact input_contain 20 15 (by decide) v hb
mask_input "14381|3032261899024822138962850563403325303236105502181048068630961011769630766965579856114996892243450152247046349017834127355803867273661746858289623584064806912508701125040722471777861885999215712549341795300227478029087591511359488|1081344"
def inputClause14382 : CNF.NClause := [(20,true),(16,true),(760,false)]
theorem inputList14382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14382 = (containClause5 20 16) := by decide
  rw [he]
  exact input_contain 20 16 (by decide) v hb
mask_input "14382|6064523798049644277925701126806650606472211004362096137261922023539261533931159712229993784486900304494092698035668254711607734547323493716579247168129613825017402250081444943555723771998431425098683590600454956058175183022718976|1114112"
def inputClause14383 : CNF.NClause := [(20,true),(17,true),(761,false)]
theorem inputList14383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14383 = (containClause5 20 17) := by decide
  rw [he]
  exact input_contain 20 17 (by decide) v hb
mask_input "14383|12129047596099288555851402253613301212944422008724192274523844047078523067862319424459987568973800608988185396071336509423215469094646987433158494336259227650034804500162889887111447543996862850197367181200909912116350366045437952|1179648"
def inputClause14384 : CNF.NClause := [(20,true),(18,true),(762,false)]
theorem inputList14384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14384 = (containClause5 20 18) := by decide
  rw [he]
  exact input_contain 20 18 (by decide) v hb
mask_input "14384|24258095192198577111702804507226602425888844017448384549047688094157046135724638848919975137947601217976370792142673018846430938189293974866316988672518455300069609000325779774222895087993725700394734362401819824232700732090875904|1310720"
def inputClause14385 : CNF.NClause := [(20,true),(19,true),(763,false)]
theorem inputList14385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14385 = (containClause5 20 19) := by decide
  rw [he]
  exact input_contain 20 19 (by decide) v hb
mask_input "14385|48516190384397154223405609014453204851777688034896769098095376188314092271449277697839950275895202435952741584285346037692861876378587949732633977345036910600139218000651559548445790175987451400789468724803639648465401464181751808|1572864"
def inputClause14386 : CNF.NClause := [(20,true),(21,true),(765,false)]
theorem inputList14386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14386 = (containClause5 20 21) := by decide
  rw [he]
  exact input_contain 20 21 (by decide) v hb
mask_input "14386|194064761537588616893622436057812819407110752139587076392381504753256369085797110791359801103580809743810966337141384150771447505514351798930535909380147642400556872002606238193783160703949805603157874899214558593861605856727007232|3145728"
def inputClause14387 : CNF.NClause := [(20,true),(22,true),(766,false)]
theorem inputList14387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14387 = (containClause5 20 22) := by decide
  rw [he]
  exact input_contain 20 22 (by decide) v hb
mask_input "14387|388129523075177233787244872115625638814221504279174152784763009506512738171594221582719602207161619487621932674282768301542895011028703597861071818760295284801113744005212476387566321407899611206315749798429117187723211713454014464|5242880"
def inputClause14388 : CNF.NClause := [(20,true),(23,true),(767,false)]
theorem inputList14388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14388 = (containClause5 20 23) := by decide
  rw [he]
  exact input_contain 20 23 (by decide) v hb
mask_input "14388|776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928|9437184"
def inputClause14389 : CNF.NClause := [(20,true),(24,true),(768,false)]
theorem inputList14389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14389 = (containClause5 20 24) := by decide
  rw [he]
  exact input_contain 20 24 (by decide) v hb
mask_input "14389|1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856|17825792"
def inputClause14391 : CNF.NClause := [(20,true),(26,true),(770,false)]
theorem inputList14391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14391 = (containClause5 20 26) := by decide
  rw [he]
  exact input_contain 20 26 (by decide) v hb
mask_input "14391|6210072369202835740595917953850010221027544068466786444556208152104203810745507545323513635314585911801950922788524292824686320176459257565777149100164724556817819904083399622201061142526393779301051996774865875003571387415264231424|68157440"
def inputClause14392 : CNF.NClause := [(20,true),(27,true),(771,false)]
theorem inputList14392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14392 = (containClause5 20 27) := by decide
  rw [he]
  exact input_contain 20 27 (by decide) v hb
mask_input "14392|12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848|135266304"
def inputClause14393 : CNF.NClause := [(20,true),(28,true),(772,false)]
theorem inputList14393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14393 = (containClause5 20 28) := by decide
  rw [he]
  exact input_contain 20 28 (by decide) v hb
mask_input "14393|24840289476811342962383671815400040884110176273867145778224832608416815242982030181294054541258343647207803691154097171298745280705837030263108596400658898227271279616333598488804244570105575117204207987099463500014285549661056925696|269484032"
def inputClause14394 : CNF.NClause := [(20,true),(29,true),(773,false)]
theorem inputList14394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14394 = (containClause5 20 29) := by decide
  rw [he]
  exact input_contain 20 29 (by decide) v hb
mask_input "14394|49680578953622685924767343630800081768220352547734291556449665216833630485964060362588109082516687294415607382308194342597490561411674060526217192801317796454542559232667196977608489140211150234408415974198927000028571099322113851392|537919488"
def inputClause14399 : CNF.NClause := [(21,true),(3,true),(778,false)]
theorem inputList14399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14399 = (containClause5 21 3) := by decide
  rw [he]
  exact input_contain 21 3 (by decide) v hb
mask_input "14399|1589778526515925949592554996185602616583051281527497329806389286938676175550849931602819490640533993421299436233862218963119697965173569936838950169642169486545361895445350303283471652486756807501069311174365664000914275178307643244544|2097160"
def inputClause14402 : CNF.NClause := [(21,true),(6,true),(781,false)]
theorem inputList14402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14402 = (containClause5 21 6) := by decide
  rw [he]
  exact input_contain 21 6 (by decide) v hb
mask_input "14402|12718228212127407596740439969484820932664410252219978638451114295509409404406799452822555925124271947370395489870897751704957583721388559494711601357137355892362895163562802426267773219894054460008554489394925312007314201426461145956352|2097216"
def inputClause14403 : CNF.NClause := [(21,true),(7,true),(782,false)]
theorem inputList14403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14403 = (containClause5 21 7) := by decide
  rw [he]
  exact input_contain 21 7 (by decide) v hb
mask_input "14403|25436456424254815193480879938969641865328820504439957276902228591018818808813598905645111850248543894740790979741795503409915167442777118989423202714274711784725790327125604852535546439788108920017108978789850624014628402852922291912704|2097280"
def inputClause14405 : CNF.NClause := [(21,true),(9,true),(784,false)]
theorem inputList14405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14405 = (containClause5 21 9) := by decide
  rw [he]
  exact input_contain 21 9 (by decide) v hb
mask_input "14405|101745825697019260773923519755878567461315282017759829107608914364075275235254395622580447400994175578963163918967182013639660669771108475957692810857098847138903161308502419410142185759152435680068435915159402496058513611411689167650816|2097664"
def inputClause14408 : CNF.NClause := [(21,true),(12,true),(787,false)]
theorem inputList14408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14408 = (containClause5 21 12) := by decide
  rw [he]
  exact input_contain 21 12 (by decide) v hb
mask_input "14408|813966605576154086191388158047028539690522256142078632860871314912602201882035164980643579207953404631705311351737456109117285358168867807661542486856790777111225290468019355281137486073219485440547487321275219968468108891293513341206528|2101248"
def inputClause14409 : CNF.NClause := [(21,true),(13,true),(788,false)]
theorem inputList14409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14409 = (containClause5 21 13) := by decide
  rw [he]
  exact input_contain 21 13 (by decide) v hb
mask_input "14409|1627933211152308172382776316094057079381044512284157265721742629825204403764070329961287158415906809263410622703474912218234570716337735615323084973713581554222450580936038710562274972146438970881094974642550439936936217782587026682413056|2105344"
def inputClause14410 : CNF.NClause := [(21,true),(14,true),(789,false)]
theorem inputList14410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14410 = (containClause5 21 14) := by decide
  rw [he]
  exact input_contain 21 14 (by decide) v hb
mask_input "14410|3255866422304616344765552632188114158762089024568314531443485259650408807528140659922574316831813618526821245406949824436469141432675471230646169947427163108444901161872077421124549944292877941762189949285100879873872435565174053364826112|2113536"
def inputClause14411 : CNF.NClause := [(21,true),(15,true),(790,false)]
theorem inputList14411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14411 = (containClause5 21 15) := by decide
  rw [he]
  exact input_contain 21 15 (by decide) v hb
mask_input "14411|6511732844609232689531105264376228317524178049136629062886970519300817615056281319845148633663627237053642490813899648872938282865350942461292339894854326216889802323744154842249099888585755883524379898570201759747744871130348106729652224|2129920"
def inputClause14412 : CNF.NClause := [(21,true),(16,true),(791,false)]
theorem inputList14412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14412
  have he : decodeClause inputClause14412 = containClause5 21 16 := by decide
  rw [he]
  exact input_contain 21 16 (by decide) v hb
mask_input "14412|13023465689218465379062210528752456635048356098273258125773941038601635230112562639690297267327254474107284981627799297745876565730701884922584679789708652433779604647488309684498199777171511767048759797140403519495489742260696213459304448|2162688"
def inputClause14413 : CNF.NClause := [(21,true),(17,true),(792,false)]
theorem inputList14413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14413
  have he : decodeClause inputClause14413 = containClause5 21 17 := by decide
  rw [he]
  exact input_contain 21 17 (by decide) v hb
mask_input "14413|26046931378436930758124421057504913270096712196546516251547882077203270460225125279380594534654508948214569963255598595491753131461403769845169359579417304867559209294976619368996399554343023534097519594280807038990979484521392426918608896|2228224"
def inputClause14414 : CNF.NClause := [(21,true),(18,true),(793,false)]
theorem inputList14414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14414 = (containClause5 21 18) := by decide
  rw [he]
  exact input_contain 21 18 (by decide) v hb
mask_input "14414|52093862756873861516248842115009826540193424393093032503095764154406540920450250558761189069309017896429139926511197190983506262922807539690338719158834609735118418589953238737992799108686047068195039188561614077981958969042784853837217792|2359296"
def inputClause14415 : CNF.NClause := [(21,true),(19,true),(794,false)]
theorem inputList14415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14415
  have he : decodeClause inputClause14415 = containClause5 21 19 := by decide
  rw [he]
  exact input_contain 21 19 (by decide) v hb
mask_input "14415|104187725513747723032497684230019653080386848786186065006191528308813081840900501117522378138618035792858279853022394381967012525845615079380677438317669219470236837179906477475985598217372094136390078377123228155963917938085569707674435584|2621440"
def inputClause14416 : CNF.NClause := [(21,true),(20,true),(795,false)]
theorem inputList14416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14416 = (containClause5 21 20) := by decide
  rw [he]
  exact input_contain 21 20 (by decide) v hb
mask_input "14416|208375451027495446064995368460039306160773697572372130012383056617626163681801002235044756277236071585716559706044788763934025051691230158761354876635338438940473674359812954951971196434744188272780156754246456311927835876171139415348871168|3145728"
end Percolation.MaskChain
