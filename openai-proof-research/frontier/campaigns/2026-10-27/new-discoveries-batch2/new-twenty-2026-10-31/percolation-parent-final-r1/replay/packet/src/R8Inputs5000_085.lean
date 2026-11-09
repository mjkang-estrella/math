import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause13959 : CNF.NClause := [(6,true),(14,true),(324,false)]
theorem inputList13959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13959 = (containClause5 6 14) := by decide
  rw [he]
  exact input_contain 6 14 (by decide) v hb
mask_input "13959|34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216|16448"
def inputClause13960 : CNF.NClause := [(6,true),(15,true),(325,false)]
theorem inputList13960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13960 = (containClause5 6 15) := by decide
  rw [he]
  exact input_contain 6 15 (by decide) v hb
mask_input "13960|68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432|32832"
def inputClause13961 : CNF.NClause := [(6,true),(16,true),(326,false)]
theorem inputList13961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13961 = (containClause5 6 16) := by decide
  rw [he]
  exact input_contain 6 16 (by decide) v hb
mask_input "13961|136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864|65600"
def inputClause13962 : CNF.NClause := [(6,true),(17,true),(327,false)]
theorem inputList13962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13962 = (containClause5 6 17) := by decide
  rw [he]
  exact input_contain 6 17 (by decide) v hb
mask_input "13962|273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728|131136"
def inputClause13963 : CNF.NClause := [(6,true),(18,true),(328,false)]
theorem inputList13963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13963 = (containClause5 6 18) := by decide
  rw [he]
  exact input_contain 6 18 (by decide) v hb
mask_input "13963|546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456|262208"
def inputClause13964 : CNF.NClause := [(6,true),(19,true),(329,false)]
theorem inputList13964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13964 = (containClause5 6 19) := by decide
  rw [he]
  exact input_contain 6 19 (by decide) v hb
mask_input "13964|1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912|524352"
def inputClause13965 : CNF.NClause := [(6,true),(20,true),(330,false)]
theorem inputList13965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13965 = (containClause5 6 20) := by decide
  rw [he]
  exact input_contain 6 20 (by decide) v hb
mask_input "13965|2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824|1048640"
def inputClause13966 : CNF.NClause := [(6,true),(21,true),(331,false)]
theorem inputList13966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13966 = (containClause5 6 21) := by decide
  rw [he]
  exact input_contain 6 21 (by decide) v hb
mask_input "13966|4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648|2097216"
def inputClause13967 : CNF.NClause := [(6,true),(22,true),(332,false)]
theorem inputList13967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13967 = (containClause5 6 22) := by decide
  rw [he]
  exact input_contain 6 22 (by decide) v hb
mask_input "13967|8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296|4194368"
def inputClause13968 : CNF.NClause := [(6,true),(23,true),(333,false)]
theorem inputList13968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13968 = (containClause5 6 23) := by decide
  rw [he]
  exact input_contain 6 23 (by decide) v hb
mask_input "13968|17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592|8388672"
def inputClause13969 : CNF.NClause := [(6,true),(24,true),(334,false)]
theorem inputList13969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13969 = (containClause5 6 24) := by decide
  rw [he]
  exact input_contain 6 24 (by decide) v hb
mask_input "13969|34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184|16777280"
def inputClause13971 : CNF.NClause := [(6,true),(26,true),(336,false)]
theorem inputList13971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13971 = (containClause5 6 26) := by decide
  rw [he]
  exact input_contain 6 26 (by decide) v hb
mask_input "13971|139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736|67108928"
def inputClause13972 : CNF.NClause := [(6,true),(27,true),(337,false)]
theorem inputList13972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13972 = (containClause5 6 27) := by decide
  rw [he]
  exact input_contain 6 27 (by decide) v hb
mask_input "13972|279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472|134217792"
def inputClause13973 : CNF.NClause := [(6,true),(28,true),(338,false)]
theorem inputList13973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13973 = (containClause5 6 28) := by decide
  rw [he]
  exact input_contain 6 28 (by decide) v hb
mask_input "13973|559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944|268435520"
def inputClause13974 : CNF.NClause := [(6,true),(29,true),(339,false)]
theorem inputList13974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13974 = (containClause5 6 29) := by decide
  rw [he]
  exact input_contain 6 29 (by decide) v hb
mask_input "13974|1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888|536870976"
def inputClause13979 : CNF.NClause := [(7,true),(3,true),(344,false)]
theorem inputList13979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13979
  have he : decodeClause inputClause13979 = containClause5 7 3 := by decide
  rw [he]
  exact input_contain 7 3 (by decide) v hb
mask_input "13979|35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416|136"
def inputClause13982 : CNF.NClause := [(7,true),(6,true),(347,false)]
theorem inputList13982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13982 = (containClause5 7 6) := by decide
  rw [he]
  exact input_contain 7 6 (by decide) v hb
mask_input "13982|286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328|192"
def inputClause13984 : CNF.NClause := [(7,true),(9,true),(350,false)]
theorem inputList13984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13984
  have he : decodeClause inputClause13984 = containClause5 7 9 := by decide
  rw [he]
  exact input_contain 7 9 (by decide) v hb
mask_input "13984|2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624|640"
def inputClause13987 : CNF.NClause := [(7,true),(12,true),(353,false)]
theorem inputList13987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13987 = (containClause5 7 12) := by decide
  rw [he]
  exact input_contain 7 12 (by decide) v hb
mask_input "13987|18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992|4224"
def inputClause13988 : CNF.NClause := [(7,true),(13,true),(354,false)]
theorem inputList13988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13988
  have he : decodeClause inputClause13988 = containClause5 7 13 := by decide
  rw [he]
  exact input_contain 7 13 (by decide) v hb
mask_input "13988|36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984|8320"
def inputClause13989 : CNF.NClause := [(7,true),(14,true),(355,false)]
theorem inputList13989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13989 = (containClause5 7 14) := by decide
  rw [he]
  exact input_contain 7 14 (by decide) v hb
mask_input "13989|73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968|16512"
def inputClause13990 : CNF.NClause := [(7,true),(15,true),(356,false)]
theorem inputList13990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13990
  have he : decodeClause inputClause13990 = containClause5 7 15 := by decide
  rw [he]
  exact input_contain 7 15 (by decide) v hb
mask_input "13990|146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936|32896"
def inputClause13991 : CNF.NClause := [(7,true),(16,true),(357,false)]
theorem inputList13991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13991
  have he : decodeClause inputClause13991 = containClause5 7 16 := by decide
  rw [he]
  exact input_contain 7 16 (by decide) v hb
mask_input "13991|293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872|65664"
def inputClause13992 : CNF.NClause := [(7,true),(17,true),(358,false)]
theorem inputList13992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13992 = (containClause5 7 17) := by decide
  rw [he]
  exact input_contain 7 17 (by decide) v hb
mask_input "13992|587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744|131200"
def inputClause13993 : CNF.NClause := [(7,true),(18,true),(359,false)]
theorem inputList13993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13993 = (containClause5 7 18) := by decide
  rw [he]
  exact input_contain 7 18 (by decide) v hb
mask_input "13993|1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488|262272"
def inputClause13994 : CNF.NClause := [(7,true),(19,true),(360,false)]
theorem inputList13994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13994
  have he : decodeClause inputClause13994 = containClause5 7 19 := by decide
  rw [he]
  exact input_contain 7 19 (by decide) v hb
mask_input "13994|2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976|524416"
def inputClause13995 : CNF.NClause := [(7,true),(20,true),(361,false)]
theorem inputList13995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13995
  have he : decodeClause inputClause13995 = containClause5 7 20 := by decide
  rw [he]
  exact input_contain 7 20 (by decide) v hb
mask_input "13995|4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952|1048704"
def inputClause13996 : CNF.NClause := [(7,true),(21,true),(362,false)]
theorem inputList13996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13996 = (containClause5 7 21) := by decide
  rw [he]
  exact input_contain 7 21 (by decide) v hb
mask_input "13996|9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904|2097280"
def inputClause13997 : CNF.NClause := [(7,true),(22,true),(363,false)]
theorem inputList13997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13997 = (containClause5 7 22) := by decide
  rw [he]
  exact input_contain 7 22 (by decide) v hb
mask_input "13997|18788340662190665823115844774314696219005460391266558965658327772257672200916867547709591987078149624255479808|4194432"
def inputClause13998 : CNF.NClause := [(7,true),(23,true),(364,false)]
theorem inputList13998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13998
  have he : decodeClause inputClause13998 = containClause5 7 23 := by decide
  rw [he]
  exact input_contain 7 23 (by decide) v hb
mask_input "13998|37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616|8388736"
def inputClause13999 : CNF.NClause := [(7,true),(24,true),(365,false)]
theorem inputList13999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13999
  have he : decodeClause inputClause13999 = containClause5 7 24 := by decide
  rw [he]
  exact input_contain 7 24 (by decide) v hb
mask_input "13999|75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232|16777344"
def inputClause14001 : CNF.NClause := [(7,true),(26,true),(367,false)]
theorem inputList14001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14001
  have he : decodeClause inputClause14001 = containClause5 7 26 := by decide
  rw [he]
  exact input_contain 7 26 (by decide) v hb
mask_input "14001|300613450595050653169853516389035139504087366260264943450533244356122755214669880763353471793250393988087676928|67108992"
def inputClause14002 : CNF.NClause := [(7,true),(27,true),(368,false)]
theorem inputList14002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14002
  have he : decodeClause inputClause14002 = containClause5 7 27 := by decide
  rw [he]
  exact input_contain 7 27 (by decide) v hb
mask_input "14002|601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856|134217856"
def inputClause14003 : CNF.NClause := [(7,true),(28,true),(369,false)]
theorem inputList14003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14003 = (containClause5 7 28) := by decide
  rw [he]
  exact input_contain 7 28 (by decide) v hb
mask_input "14003|1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712|268435584"
def inputClause14004 : CNF.NClause := [(7,true),(29,true),(370,false)]
theorem inputList14004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14004
  have he : decodeClause inputClause14004 = containClause5 7 29 := by decide
  rw [he]
  exact input_contain 7 29 (by decide) v hb
mask_input "14004|2404907604760405225358828131112281116032698930082119547604265954848982041717359046106827774346003151904701415424|536871040"
def inputClause14039 : CNF.NClause := [(9,true),(3,true),(406,false)]
theorem inputList14039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14039
  have he : decodeClause inputClause14039 = containClause5 9 3 := by decide
  rw [he]
  exact input_contain 9 3 (by decide) v hb
mask_input "14039|165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064|520"
def inputClause14042 : CNF.NClause := [(9,true),(6,true),(409,false)]
theorem inputList14042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14042 = (containClause5 9 6) := by decide
  rw [he]
  exact input_contain 9 6 (by decide) v hb
mask_input "14042|1322111937580497197903830616065542079656809365928562438569297590548811582472622691650378420879430569695182424050046716608512|576"
def inputClause14043 : CNF.NClause := [(9,true),(7,true),(410,false)]
theorem inputList14043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14043 = (containClause5 9 7) := by decide
  rw [he]
  exact input_contain 9 7 (by decide) v hb
mask_input "14043|2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024|640"
def inputClause14047 : CNF.NClause := [(9,true),(12,true),(415,false)]
theorem inputList14047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14047
  have he : decodeClause inputClause14047 = containClause5 9 12 := by decide
  rw [he]
  exact input_contain 9 12 (by decide) v hb
mask_input "14047|84615164005151820665845159428194693098035799419427996068435045795123941278247852265624218936283556460491675139202989862944768|4608"
def inputClause14048 : CNF.NClause := [(9,true),(13,true),(416,false)]
theorem inputList14048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14048 = (containClause5 9 13) := by decide
  rw [he]
  exact input_contain 9 13 (by decide) v hb
mask_input "14048|169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536|8704"
end Percolation.MaskChain
