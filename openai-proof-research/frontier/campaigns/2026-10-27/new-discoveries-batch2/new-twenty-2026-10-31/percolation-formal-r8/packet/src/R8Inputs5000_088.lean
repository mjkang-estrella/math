import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14236 : CNF.NClause := [(15,true),(21,true),(610,false)]
theorem inputList14236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14236 = (containClause5 15 21) := by decide
  rw [he]
  exact input_contain 15 21 (by decide) v hb
mask_input "14236|4249103942534136789516705652419749018636744941816255385595553105603228478886817941913300018121834285351114635889972008122772634701221657915276159830132698815550650166683145752253825024|2129920"
def inputClause14237 : CNF.NClause := [(15,true),(22,true),(611,false)]
theorem inputList14237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14237 = (containClause5 15 22) := by decide
  rw [he]
  exact input_contain 15 22 (by decide) v hb
mask_input "14237|8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291504507650048|4227072"
def inputClause14238 : CNF.NClause := [(15,true),(23,true),(612,false)]
theorem inputList14238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14238 = (containClause5 15 23) := by decide
  rw [he]
  exact input_contain 15 23 (by decide) v hb
mask_input "14238|16996415770136547158066822609678996074546979767265021542382212422412913915547271767653200072487337141404458543559888032491090538804886631661104639320530795262202600666732583009015300096|8421376"
def inputClause14239 : CNF.NClause := [(15,true),(24,true),(613,false)]
theorem inputList14239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14239 = (containClause5 15 24) := by decide
  rw [he]
  exact input_contain 15 24 (by decide) v hb
mask_input "14239|33992831540273094316133645219357992149093959534530043084764424844825827831094543535306400144974674282808917087119776064982181077609773263322209278641061590524405201333465166018030600192|16809984"
def inputClause14241 : CNF.NClause := [(15,true),(26,true),(615,false)]
theorem inputList14241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14241 = (containClause5 15 26) := by decide
  rw [he]
  exact input_contain 15 26 (by decide) v hb
mask_input "14241|135971326161092377264534580877431968596375838138120172339057699379303311324378174141225600579898697131235668348479104259928724310439093053288837114564246362097620805333860664072122400768|67141632"
def inputClause14242 : CNF.NClause := [(15,true),(27,true),(616,false)]
theorem inputList14242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14242 = (containClause5 15 27) := by decide
  rw [he]
  exact input_contain 15 27 (by decide) v hb
mask_input "14242|271942652322184754529069161754863937192751676276240344678115398758606622648756348282451201159797394262471336696958208519857448620878186106577674229128492724195241610667721328144244801536|134250496"
def inputClause14243 : CNF.NClause := [(15,true),(28,true),(617,false)]
theorem inputList14243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14243 = (containClause5 15 28) := by decide
  rw [he]
  exact input_contain 15 28 (by decide) v hb
mask_input "14243|543885304644369509058138323509727874385503352552480689356230797517213245297512696564902402319594788524942673393916417039714897241756372213155348458256985448390483221335442656288489603072|268468224"
def inputClause14244 : CNF.NClause := [(15,true),(29,true),(618,false)]
theorem inputList14244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14244 = (containClause5 15 29) := by decide
  rw [he]
  exact input_contain 15 29 (by decide) v hb
mask_input "14244|1087770609288739018116276647019455748771006705104961378712461595034426490595025393129804804639189577049885346787832834079429794483512744426310696916513970896780966442670885312576979206144|536903680"
def inputClause14249 : CNF.NClause := [(16,true),(3,true),(623,false)]
theorem inputList14249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14249 = (containClause5 16 3) := by decide
  rw [he]
  exact input_contain 16 3 (by decide) v hb
mask_input "14249|34808659497239648579720852704622583960672214563358764118798771041101647699040812580153753748454066465596331097210650690541753423472407821641942301328447068696990926165468330002463334596608|65544"
def inputClause14252 : CNF.NClause := [(16,true),(6,true),(626,false)]
theorem inputList14252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14252 = (containClause5 16 6) := by decide
  rw [he]
  exact input_contain 16 6 (by decide) v hb
mask_input "14252|278469275977917188637766821636980671685377716506870112950390168328813181592326500641230029987632531724770648777685205524334027387779262573135538410627576549575927409323746640019706676772864|65600"
def inputClause14253 : CNF.NClause := [(16,true),(7,true),(627,false)]
theorem inputList14253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14253 = (containClause5 16 7) := by decide
  rw [he]
  exact input_contain 16 7 (by decide) v hb
mask_input "14253|556938551955834377275533643273961343370755433013740225900780336657626363184653001282460059975265063449541297555370411048668054775558525146271076821255153099151854818647493280039413353545728|65664"
def inputClause14255 : CNF.NClause := [(16,true),(9,true),(629,false)]
theorem inputList14255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14255 = (containClause5 16 9) := by decide
  rw [he]
  exact input_contain 16 9 (by decide) v hb
mask_input "14255|2227754207823337509102134573095845373483021732054960903603121346630505452738612005129840239901060253798165190221481644194672219102234100585084307285020612396607419274589973120157653414182912|66048"
def inputClause14258 : CNF.NClause := [(16,true),(12,true),(632,false)]
theorem inputList14258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14258 = (containClause5 16 12) := by decide
  rw [he]
  exact input_contain 16 12 (by decide) v hb
mask_input "14258|17822033662586700072817076584766762987864173856439687228824970773044043621908896041038721919208482030385321521771853153557377752817872804680674458280164899172859354196719784961261227313463296|69632"
def inputClause14259 : CNF.NClause := [(16,true),(13,true),(633,false)]
theorem inputList14259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14259 = (containClause5 16 13) := by decide
  rw [he]
  exact input_contain 16 13 (by decide) v hb
mask_input "14259|35644067325173400145634153169533525975728347712879374457649941546088087243817792082077443838416964060770643043543706307114755505635745609361348916560329798345718708393439569922522454626926592|73728"
def inputClause14260 : CNF.NClause := [(16,true),(14,true),(634,false)]
theorem inputList14260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14260 = (containClause5 16 14) := by decide
  rw [he]
  exact input_contain 16 14 (by decide) v hb
mask_input "14260|71288134650346800291268306339067051951456695425758748915299883092176174487635584164154887676833928121541286087087412614229511011271491218722697833120659596691437416786879139845044909253853184|81920"
def inputClause14261 : CNF.NClause := [(16,true),(15,true),(635,false)]
theorem inputList14261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14261 = (containClause5 16 15) := by decide
  rw [he]
  exact input_contain 16 15 (by decide) v hb
mask_input "14261|142576269300693600582536612678134103902913390851517497830599766184352348975271168328309775353667856243082572174174825228459022022542982437445395666241319193382874833573758279690089818507706368|98304"
def inputClause14262 : CNF.NClause := [(16,true),(17,true),(637,false)]
theorem inputList14262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14262 = (containClause5 16 17) := by decide
  rw [he]
  exact input_contain 16 17 (by decide) v hb
mask_input "14262|570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472|196608"
def inputClause14263 : CNF.NClause := [(16,true),(18,true),(638,false)]
theorem inputList14263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14263 = (containClause5 16 18) := by decide
  rw [he]
  exact input_contain 16 18 (by decide) v hb
mask_input "14263|1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944|327680"
def inputClause14264 : CNF.NClause := [(16,true),(19,true),(639,false)]
theorem inputList14264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14264 = (containClause5 16 19) := by decide
  rw [he]
  exact input_contain 16 19 (by decide) v hb
mask_input "14264|2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888|589824"
def inputClause14265 : CNF.NClause := [(16,true),(20,true),(640,false)]
theorem inputList14265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14265 = (containClause5 16 20) := by decide
  rw [he]
  exact input_contain 16 20 (by decide) v hb
mask_input "14265|4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776|1114112"
def inputClause14266 : CNF.NClause := [(16,true),(21,true),(641,false)]
theorem inputList14266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14266 = (containClause5 16 21) := by decide
  rw [he]
  exact input_contain 16 21 (by decide) v hb
mask_input "14266|9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748384493207552|2162688"
def inputClause14267 : CNF.NClause := [(16,true),(22,true),(642,false)]
theorem inputList14267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14267 = (containClause5 16 22) := by decide
  rw [he]
  exact input_contain 16 22 (by decide) v hb
mask_input "14267|18249762470488780874564686422801165299572914028994239722316770071597100668834709546023651245269485599114569238294377629242754818885501751993010645278888856753007978697441059800331496768986415104|4259840"
def inputClause14268 : CNF.NClause := [(16,true),(23,true),(643,false)]
theorem inputList14268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14268 = (containClause5 16 23) := by decide
  rw [he]
  exact input_contain 16 23 (by decide) v hb
mask_input "14268|36499524940977561749129372845602330599145828057988479444633540143194201337669419092047302490538971198229138476588755258485509637771003503986021290557777713506015957394882119600662993537972830208|8454144"
def inputClause14269 : CNF.NClause := [(16,true),(24,true),(644,false)]
theorem inputList14269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14269 = (containClause5 16 24) := by decide
  rw [he]
  exact input_contain 16 24 (by decide) v hb
mask_input "14269|72999049881955123498258745691204661198291656115976958889267080286388402675338838184094604981077942396458276953177510516971019275542007007972042581115555427012031914789764239201325987075945660416|16842752"
def inputClause14271 : CNF.NClause := [(16,true),(26,true),(646,false)]
theorem inputList14271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14271 = (containClause5 16 26) := by decide
  rw [he]
  exact input_contain 16 26 (by decide) v hb
mask_input "14271|291996199527820493993034982764818644793166624463907835557068321145553610701355352736378419924311769585833107812710042067884077102168028031888170324462221708048127659159056956805303948303782641664|67174400"
def inputClause14272 : CNF.NClause := [(16,true),(27,true),(647,false)]
theorem inputList14272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14272 = (containClause5 16 27) := by decide
  rw [he]
  exact input_contain 16 27 (by decide) v hb
mask_input "14272|583992399055640987986069965529637289586333248927815671114136642291107221402710705472756839848623539171666215625420084135768154204336056063776340648924443416096255318318113913610607896607565283328|134283264"
def inputClause14273 : CNF.NClause := [(16,true),(28,true),(648,false)]
theorem inputList14273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14273 = (containClause5 16 28) := by decide
  rw [he]
  exact input_contain 16 28 (by decide) v hb
mask_input "14273|1167984798111281975972139931059274579172666497855631342228273284582214442805421410945513679697247078343332431250840168271536308408672112127552681297848886832192510636636227827221215793215130566656|268500992"
def inputClause14274 : CNF.NClause := [(16,true),(29,true),(649,false)]
theorem inputList14274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14274 = (containClause5 16 29) := by decide
  rw [he]
  exact input_contain 16 29 (by decide) v hb
mask_input "14274|2335969596222563951944279862118549158345332995711262684456546569164428885610842821891027359394494156686664862501680336543072616817344224255105362595697773664385021273272455654442431586430261133312|536936448"
def inputClause14279 : CNF.NClause := [(17,true),(3,true),(654,false)]
theorem inputList14279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14279 = (containClause5 17 3) := by decide
  rw [he]
  exact input_contain 17 3 (by decide) v hb
mask_input "14279|74751027079122046462216955587793573067050655862760405902609490213261724339546970300512875500623813013973275600053770769378323738155015176163371603062328757260320680744718580942157810765768356265984|131080"
def inputClause14282 : CNF.NClause := [(17,true),(6,true),(657,false)]
theorem inputList14282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14282
  have he : decodeClause inputClause14282 = containClause5 17 6 := by decide
  rw [he]
  exact input_contain 17 6 (by decide) v hb
mask_input "14282|598008216632976371697735644702348584536405246902083247220875921706093794716375762404103004004990504111786204800430166155026589905240121409306972824498630058082565445957748647537262486126146850127872|131136"
def inputClause14283 : CNF.NClause := [(17,true),(7,true),(658,false)]
theorem inputList14283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14283 = (containClause5 17 7) := by decide
  rw [he]
  exact input_contain 17 7 (by decide) v hb
mask_input "14283|1196016433265952743395471289404697169072810493804166494441751843412187589432751524808206008009981008223572409600860332310053179810480242818613945648997260116165130891915497295074524972252293700255744|131200"
def inputClause14285 : CNF.NClause := [(17,true),(9,true),(660,false)]
theorem inputList14285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14285 = (containClause5 17 9) := by decide
  rw [he]
  exact input_contain 17 9 (by decide) v hb
mask_input "14285|4784065733063810973581885157618788676291241975216665977767007373648750357731006099232824032039924032894289638403441329240212719241920971274455782595989040464660523567661989180298099889009174801022976|131584"
def inputClause14288 : CNF.NClause := [(17,true),(12,true),(663,false)]
theorem inputList14288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14288 = (containClause5 17 12) := by decide
  rw [he]
  exact input_contain 17 12 (by decide) v hb
mask_input "14288|38272525864510487788655081260950309410329935801733327822136058989190002861848048793862592256319392263154317107227530633921701753935367770195646260767912323717284188541295913442384799112073398408183808|135168"
def inputClause14289 : CNF.NClause := [(17,true),(13,true),(664,false)]
theorem inputList14289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14289 = (containClause5 17 13) := by decide
  rw [he]
  exact input_contain 17 13 (by decide) v hb
mask_input "14289|76545051729020975577310162521900618820659871603466655644272117978380005723696097587725184512638784526308634214455061267843403507870735540391292521535824647434568377082591826884769598224146796816367616|139264"
def inputClause14290 : CNF.NClause := [(17,true),(14,true),(665,false)]
theorem inputList14290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14290 = (containClause5 17 14) := by decide
  rw [he]
  exact input_contain 17 14 (by decide) v hb
mask_input "14290|153090103458041951154620325043801237641319743206933311288544235956760011447392195175450369025277569052617268428910122535686807015741471080782585043071649294869136754165183653769539196448293593632735232|147456"
def inputClause14291 : CNF.NClause := [(17,true),(15,true),(666,false)]
theorem inputList14291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14291 = (containClause5 17 15) := by decide
  rw [he]
  exact input_contain 17 15 (by decide) v hb
mask_input "14291|306180206916083902309240650087602475282639486413866622577088471913520022894784390350900738050555138105234536857820245071373614031482942161565170086143298589738273508330367307539078392896587187265470464|163840"
def inputClause14292 : CNF.NClause := [(17,true),(16,true),(667,false)]
theorem inputList14292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14292 = (containClause5 17 16) := by decide
  rw [he]
  exact input_contain 17 16 (by decide) v hb
mask_input "14292|612360413832167804618481300175204950565278972827733245154176943827040045789568780701801476101110276210469073715640490142747228062965884323130340172286597179476547016660734615078156785793174374530940928|196608"
def inputClause14293 : CNF.NClause := [(17,true),(18,true),(669,false)]
theorem inputList14293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14293 = (containClause5 17 18) := by decide
  rw [he]
  exact input_contain 17 18 (by decide) v hb
mask_input "14293|2449441655328671218473925200700819802261115891310932980616707775308160183158275122807205904404441104841876294862561960570988912251863537292521360689146388717906188066642938460312627143172697498123763712|393216"
def inputClause14294 : CNF.NClause := [(17,true),(19,true),(670,false)]
theorem inputList14294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14294
  have he : decodeClause inputClause14294 = containClause5 17 19 := by decide
  rw [he]
  exact input_contain 17 19 (by decide) v hb
mask_input "14294|4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727074585042721378292777435812376133285876920625254286345394996247527424|655360"
def inputClause14295 : CNF.NClause := [(17,true),(20,true),(671,false)]
theorem inputList14295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14295
  have he : decodeClause inputClause14295 = containClause5 17 20 := by decide
  rw [he]
  exact input_contain 17 20 (by decide) v hb
mask_input "14295|9797766621314684873895700802803279209044463565243731922466831101232640732633100491228823617617764419367505179450247842283955649007454149170085442756585554871624752266571753841250508572690789992495054848|1179648"
end Percolation.MaskChain
