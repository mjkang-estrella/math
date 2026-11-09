import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14034 : CNF.NClause := [(8,true),(29,true),(401,false)]
theorem inputList14034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14034
  have he : decodeClause inputClause14034 = containClause5 8 29 := by decide
  rw [he]
  exact input_contain 8 29 (by decide) v hb
mask_input "14034|5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343945494986752|536871168"
def inputClause14037 : CNF.NClause := [(9,true),(1,true),(404,false)]
theorem inputList14037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14037 = (containClause5 9 1) := by decide
  rw [he]
  exact input_contain 9 1 (by decide) v hb
mask_input "14037|41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016|514"
def inputClause14038 : CNF.NClause := [(9,true),(2,true),(405,false)]
theorem inputList14038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14038 = (containClause5 9 2) := by decide
  rw [he]
  exact input_contain 9 2 (by decide) v hb
mask_input "14038|82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032|516"
def inputClause14041 : CNF.NClause := [(9,true),(5,true),(408,false)]
theorem inputList14041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14041 = (containClause5 9 5) := by decide
  rw [he]
  exact input_contain 9 5 (by decide) v hb
mask_input "14041|661055968790248598951915308032771039828404682964281219284648795274405791236311345825189210439715284847591212025023358304256|544"
def inputClause14044 : CNF.NClause := [(9,true),(8,true),(411,false)]
theorem inputList14044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14044
  have he : decodeClause inputClause14044 = containClause5 9 8 := by decide
  rw [he]
  exact input_contain 9 8 (by decide) v hb
mask_input "14044|5288447750321988791615322464262168318627237463714249754277190362195246329890490766601513683517722278780729696200186866434048|768"
def inputClause14045 : CNF.NClause := [(9,true),(10,true),(413,false)]
theorem inputList14045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14045 = (containClause5 9 10) := by decide
  rw [he]
  exact input_contain 9 10 (by decide) v hb
mask_input "14045|21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192|1536"
def inputClause14046 : CNF.NClause := [(9,true),(11,true),(414,false)]
theorem inputList14046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14046 = (containClause5 9 11) := by decide
  rw [he]
  exact input_contain 9 11 (by decide) v hb
mask_input "14046|42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384|2560"
def inputClause14067 : CNF.NClause := [(10,true),(1,true),(435,false)]
theorem inputList14067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14067
  have he : decodeClause inputClause14067 = containClause5 10 1 := by decide
  rw [he]
  exact input_contain 10 1 (by decide) v hb
mask_input "14067|88725430211866075506509253892578678509965986412026130405455346579667881849780019937279180995332466499116518750764914298527173050368|1026"
def inputClause14068 : CNF.NClause := [(10,true),(2,true),(436,false)]
theorem inputList14068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14068
  have he : decodeClause inputClause14068 = containClause5 10 2 := by decide
  rw [he]
  exact input_contain 10 2 (by decide) v hb
mask_input "14068|177450860423732151013018507785157357019931972824052260810910693159335763699560039874558361990664932998233037501529828597054346100736|1028"
def inputClause14071 : CNF.NClause := [(10,true),(5,true),(439,false)]
theorem inputList14071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14071 = (containClause5 10 5) := by decide
  rw [he]
  exact input_contain 10 5 (by decide) v hb
mask_input "14071|1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888|1056"
def inputClause14072 : CNF.NClause := [(10,true),(6,true),(440,false)]
theorem inputList14072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14072
  have he : decodeClause inputClause14072 = containClause5 10 6 := by decide
  rw [he]
  exact input_contain 10 6 (by decide) v hb
mask_input "14072|2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776|1088"
def inputClause14073 : CNF.NClause := [(10,true),(7,true),(441,false)]
theorem inputList14073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14073
  have he : decodeClause inputClause14073 = containClause5 10 7 := by decide
  rw [he]
  exact input_contain 10 7 (by decide) v hb
mask_input "14073|5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552|1152"
def inputClause14074 : CNF.NClause := [(10,true),(8,true),(442,false)]
theorem inputList14074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14074
  have he : decodeClause inputClause14074 = containClause5 10 8 := by decide
  rw [he]
  exact input_contain 10 8 (by decide) v hb
mask_input "14074|11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104|1280"
def inputClause14075 : CNF.NClause := [(10,true),(9,true),(443,false)]
theorem inputList14075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14075
  have he : decodeClause inputClause14075 = containClause5 10 9 := by decide
  rw [he]
  exact input_contain 10 9 (by decide) v hb
mask_input "14075|22713710134237715329666368996500141698551292521478689383796568724394977753543685103943470334805111423773828800195818060422956300894208|1536"
def inputClause14076 : CNF.NClause := [(10,true),(11,true),(445,false)]
theorem inputList14076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14076
  have he : decodeClause inputClause14076 = containClause5 10 11 := by decide
  rw [he]
  exact input_contain 10 11 (by decide) v hb
mask_input "14076|90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832|3072"
def inputClause14077 : CNF.NClause := [(10,true),(12,true),(446,false)]
theorem inputList14077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14077
  have he : decodeClause inputClause14077 = containClause5 10 12 := by decide
  rw [he]
  exact input_contain 10 12 (by decide) v hb
mask_input "14077|181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664|5120"
def inputClause14078 : CNF.NClause := [(10,true),(13,true),(447,false)]
theorem inputList14078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14078
  have he : decodeClause inputClause14078 = containClause5 10 13 := by decide
  rw [he]
  exact input_contain 10 13 (by decide) v hb
mask_input "14078|363419362147803445274661903944002267176820680343659030140745099590319644056698961663095525356881782780381260803133088966767300814307328|9216"
def inputClause14079 : CNF.NClause := [(10,true),(14,true),(448,false)]
theorem inputList14079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14079
  have he : decodeClause inputClause14079 = containClause5 10 14 := by decide
  rw [he]
  exact input_contain 10 14 (by decide) v hb
mask_input "14079|726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656|17408"
def inputClause14081 : CNF.NClause := [(10,true),(16,true),(450,false)]
theorem inputList14081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14081
  have he : decodeClause inputClause14081 = containClause5 10 16 := by decide
  rw [he]
  exact input_contain 10 16 (by decide) v hb
mask_input "14081|2907354897182427562197295231552018137414565442749272241125960796722557152453591693304764202855054262243050086425064711734138406514458624|66560"
def inputClause14083 : CNF.NClause := [(10,true),(18,true),(452,false)]
theorem inputList14083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14083 = (containClause5 10 18) := by decide
  rw [he]
  exact input_contain 10 18 (by decide) v hb
mask_input "14083|11629419588729710248789180926208072549658261770997088964503843186890228609814366773219056811420217048972200345700258846936553626057834496|263168"
def inputClause14084 : CNF.NClause := [(10,true),(19,true),(453,false)]
theorem inputList14084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14084
  have he : decodeClause inputClause14084 = containClause5 10 19 := by decide
  rw [he]
  exact input_contain 10 19 (by decide) v hb
mask_input "14084|23258839177459420497578361852416145099316523541994177929007686373780457219628733546438113622840434097944400691400517693873107252115668992|525312"
def inputClause14086 : CNF.NClause := [(10,true),(21,true),(455,false)]
theorem inputList14086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14086
  have he : decodeClause inputClause14086 = containClause5 10 21 := by decide
  rw [he]
  exact input_contain 10 21 (by decide) v hb
mask_input "14086|93035356709837681990313447409664580397266094167976711716030745495121828878514934185752454491361736391777602765602070775492429008462675968|2098176"
def inputClause14087 : CNF.NClause := [(10,true),(22,true),(456,false)]
theorem inputList14087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14087 = (containClause5 10 22) := by decide
  rw [he]
  exact input_contain 10 22 (by decide) v hb
mask_input "14087|186070713419675363980626894819329160794532188335953423432061490990243657757029868371504908982723472783555205531204141550984858016925351936|4195328"
def inputClause14089 : CNF.NClause := [(10,true),(24,true),(458,false)]
theorem inputList14089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14089
  have he : decodeClause inputClause14089 = containClause5 10 24 := by decide
  rw [he]
  exact input_contain 10 24 (by decide) v hb
mask_input "14089|744282853678701455922507579277316643178128753343813693728245963960974631028119473486019635930893891134220822124816566203939432067701407744|16778240"
def inputClause14091 : CNF.NClause := [(10,true),(26,true),(460,false)]
theorem inputList14091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14091
  have he : decodeClause inputClause14091 = containClause5 10 26 := by decide
  rw [he]
  exact input_contain 10 26 (by decide) v hb
mask_input "14091|2977131414714805823690030317109266572712515013375254774912983855843898524112477893944078543723575564536883288499266264815757728270805630976|67109888"
def inputClause14093 : CNF.NClause := [(10,true),(28,true),(462,false)]
theorem inputList14093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14093
  have he : decodeClause inputClause14093 = containClause5 10 28 := by decide
  rw [he]
  exact input_contain 10 28 (by decide) v hb
mask_input "14093|11908525658859223294760121268437066290850060053501019099651935423375594096449911575776314174894302258147533153997065059263030913083222523904|268436480"
def inputClause14094 : CNF.NClause := [(10,true),(29,true),(463,false)]
theorem inputList14094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14094
  have he : decodeClause inputClause14094 = containClause5 10 29 := by decide
  rw [he]
  exact input_contain 10 29 (by decide) v hb
mask_input "14094|23817051317718446589520242536874132581700120107002038199303870846751188192899823151552628349788604516295066307994130118526061826166445047808|536871936"
def inputClause14097 : CNF.NClause := [(11,true),(1,true),(466,false)]
theorem inputList14097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14097 = (containClause5 11 1) := by decide
  rw [he]
  exact input_contain 11 1 (by decide) v hb
mask_input "14097|190536410541747572716161940294993060653600960856016305594430966774009505543198585212421026798308836130360530463953040948208494609331560382464|2050"
def inputClause14098 : CNF.NClause := [(11,true),(2,true),(467,false)]
theorem inputList14098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14098
  have he : decodeClause inputClause14098 = containClause5 11 2 := by decide
  rw [he]
  exact input_contain 11 2 (by decide) v hb
mask_input "14098|381072821083495145432323880589986121307201921712032611188861933548019011086397170424842053596617672260721060927906081896416989218663120764928|2052"
def inputClause14101 : CNF.NClause := [(11,true),(5,true),(470,false)]
theorem inputList14101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14101
  have he : decodeClause inputClause14101 = containClause5 11 5 := by decide
  rw [he]
  exact input_contain 11 5 (by decide) v hb
mask_input "14101|3048582568667961163458591044719888970457615373696260889510895468384152088691177363398736428772941378085768487423248655171335913749304966119424|2080"
def inputClause14102 : CNF.NClause := [(11,true),(6,true),(471,false)]
theorem inputList14102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14102 = (containClause5 11 6) := by decide
  rw [he]
  exact input_contain 11 6 (by decide) v hb
mask_input "14102|6097165137335922326917182089439777940915230747392521779021790936768304177382354726797472857545882756171536974846497310342671827498609932238848|2112"
def inputClause14103 : CNF.NClause := [(11,true),(7,true),(472,false)]
theorem inputList14103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14103
  have he : decodeClause inputClause14103 = containClause5 11 7 := by decide
  rw [he]
  exact input_contain 11 7 (by decide) v hb
mask_input "14103|12194330274671844653834364178879555881830461494785043558043581873536608354764709453594945715091765512343073949692994620685343654997219864477696|2176"
def inputClause14104 : CNF.NClause := [(11,true),(8,true),(473,false)]
theorem inputList14104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14104 = (containClause5 11 8) := by decide
  rw [he]
  exact input_contain 11 8 (by decide) v hb
mask_input "14104|24388660549343689307668728357759111763660922989570087116087163747073216709529418907189891430183531024686147899385989241370687309994439728955392|2304"
def inputClause14105 : CNF.NClause := [(11,true),(9,true),(474,false)]
theorem inputList14105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14105
  have he : decodeClause inputClause14105 = containClause5 11 9 := by decide
  rw [he]
  exact input_contain 11 9 (by decide) v hb
mask_input "14105|48777321098687378615337456715518223527321845979140174232174327494146433419058837814379782860367062049372295798771978482741374619988879457910784|2560"
def inputClause14106 : CNF.NClause := [(11,true),(10,true),(475,false)]
theorem inputList14106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14106
  have he : decodeClause inputClause14106 = containClause5 11 10 := by decide
  rw [he]
  exact input_contain 11 10 (by decide) v hb
mask_input "14106|97554642197374757230674913431036447054643691958280348464348654988292866838117675628759565720734124098744591597543956965482749239977758915821568|3072"
def inputClause14107 : CNF.NClause := [(11,true),(12,true),(477,false)]
theorem inputList14107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14107
  have he : decodeClause inputClause14107 = containClause5 11 12 := by decide
  rw [he]
  exact input_contain 11 12 (by decide) v hb
mask_input "14107|390218568789499028922699653724145788218574767833121393857394619953171467352470702515038262882936496394978366390175827861930996959911035663286272|6144"
def inputClause14108 : CNF.NClause := [(11,true),(13,true),(478,false)]
theorem inputList14108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14108
  have he : decodeClause inputClause14108 = containClause5 11 13 := by decide
  rw [he]
  exact input_contain 11 13 (by decide) v hb
mask_input "14108|780437137578998057845399307448291576437149535666242787714789239906342934704941405030076525765872992789956732780351655723861993919822071326572544|10240"
def inputClause14109 : CNF.NClause := [(11,true),(14,true),(479,false)]
theorem inputList14109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14109
  have he : decodeClause inputClause14109 = containClause5 11 14 := by decide
  rw [he]
  exact input_contain 11 14 (by decide) v hb
mask_input "14109|1560874275157996115690798614896583152874299071332485575429578479812685869409882810060153051531745985579913465560703311447723987839644142653145088|18432"
def inputClause14111 : CNF.NClause := [(11,true),(16,true),(481,false)]
theorem inputList14111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14111
  have he : decodeClause inputClause14111 = containClause5 11 16 := by decide
  rw [he]
  exact input_contain 11 16 (by decide) v hb
mask_input "14111|6243497100631984462763194459586332611497196285329942301718313919250743477639531240240612206126983942319653862242813245790895951358576570612580352|67584"
def inputClause14113 : CNF.NClause := [(11,true),(18,true),(483,false)]
theorem inputList14113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14113
  have he : decodeClause inputClause14113 = containClause5 11 18 := by decide
  rw [he]
  exact input_contain 11 18 (by decide) v hb
mask_input "14113|24973988402527937851052777838345330445988785141319769206873255677002973910558124960962448824507935769278615448971252983163583805434306282450321408|264192"
end Percolation.MaskChain
