import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause13801 : CNF.NClause := [(1,true),(6,true),(161,false)]
theorem inputList13801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13801 = (containClause5 1 6) := by decide
  rw [he]
  exact input_contain 1 6 (by decide) v hb
mask_input "13801|2923003274661805836407369665432566039311865085952|66"
def inputClause13802 : CNF.NClause := [(1,true),(7,true),(162,false)]
theorem inputList13802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13802 = (containClause5 1 7) := by decide
  rw [he]
  exact input_contain 1 7 (by decide) v hb
mask_input "13802|5846006549323611672814739330865132078623730171904|130"
def inputClause13803 : CNF.NClause := [(1,true),(8,true),(163,false)]
theorem inputList13803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13803 = (containClause5 1 8) := by decide
  rw [he]
  exact input_contain 1 8 (by decide) v hb
mask_input "13803|11692013098647223345629478661730264157247460343808|258"
def inputClause13804 : CNF.NClause := [(1,true),(9,true),(164,false)]
theorem inputList13804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13804 = (containClause5 1 9) := by decide
  rw [he]
  exact input_contain 1 9 (by decide) v hb
mask_input "13804|23384026197294446691258957323460528314494920687616|514"
def inputClause13805 : CNF.NClause := [(1,true),(10,true),(165,false)]
theorem inputList13805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13805 = (containClause5 1 10) := by decide
  rw [he]
  exact input_contain 1 10 (by decide) v hb
mask_input "13805|46768052394588893382517914646921056628989841375232|1026"
def inputClause13806 : CNF.NClause := [(1,true),(11,true),(166,false)]
theorem inputList13806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13806 = (containClause5 1 11) := by decide
  rw [he]
  exact input_contain 1 11 (by decide) v hb
mask_input "13806|93536104789177786765035829293842113257979682750464|2050"
def inputClause13807 : CNF.NClause := [(1,true),(12,true),(167,false)]
theorem inputList13807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13807 = (containClause5 1 12) := by decide
  rw [he]
  exact input_contain 1 12 (by decide) v hb
mask_input "13807|187072209578355573530071658587684226515959365500928|4098"
def inputClause13808 : CNF.NClause := [(1,true),(13,true),(168,false)]
theorem inputList13808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13808 = (containClause5 1 13) := by decide
  rw [he]
  exact input_contain 1 13 (by decide) v hb
mask_input "13808|374144419156711147060143317175368453031918731001856|8194"
def inputClause13811 : CNF.NClause := [(1,true),(16,true),(171,false)]
theorem inputList13811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13811 = (containClause5 1 16) := by decide
  rw [he]
  exact input_contain 1 16 (by decide) v hb
mask_input "13811|2993155353253689176481146537402947624255349848014848|65538"
def inputClause13816 : CNF.NClause := [(1,true),(21,true),(176,false)]
theorem inputList13816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13816 = (containClause5 1 21) := by decide
  rw [he]
  exact input_contain 1 21 (by decide) v hb
mask_input "13816|95780971304118053647396689196894323976171195136475136|2097154"
def inputClause13819 : CNF.NClause := [(1,true),(24,true),(179,false)]
theorem inputList13819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13819 = (containClause5 1 24) := by decide
  rw [he]
  exact input_contain 1 24 (by decide) v hb
mask_input "13819|766247770432944429179173513575154591809369561091801088|16777218"
def inputClause13821 : CNF.NClause := [(1,true),(26,true),(181,false)]
theorem inputList13821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13821 = (containClause5 1 26) := by decide
  rw [he]
  exact input_contain 1 26 (by decide) v hb
mask_input "13821|3064991081731777716716694054300618367237478244367204352|67108866"
def inputClause13827 : CNF.NClause := [(2,true),(1,true),(187,false)]
theorem inputList13827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13827 = (containClause5 2 1) := by decide
  rw [he]
  exact input_contain 2 1 (by decide) v hb
mask_input "13827|196159429230833773869868419475239575503198607639501078528|6"
def inputClause13830 : CNF.NClause := [(2,true),(5,true),(191,false)]
theorem inputList13830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13830
  have he : decodeClause inputClause13830 = containClause5 2 5 := by decide
  rw [he]
  exact input_contain 2 5 (by decide) v hb
mask_input "13830|3138550867693340381917894711603833208051177722232017256448|36"
def inputClause13831 : CNF.NClause := [(2,true),(6,true),(192,false)]
theorem inputList13831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13831 = (containClause5 2 6) := by decide
  rw [he]
  exact input_contain 2 6 (by decide) v hb
mask_input "13831|6277101735386680763835789423207666416102355444464034512896|68"
def inputClause13832 : CNF.NClause := [(2,true),(7,true),(193,false)]
theorem inputList13832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13832 = (containClause5 2 7) := by decide
  rw [he]
  exact input_contain 2 7 (by decide) v hb
mask_input "13832|12554203470773361527671578846415332832204710888928069025792|132"
def inputClause13833 : CNF.NClause := [(2,true),(8,true),(194,false)]
theorem inputList13833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13833 = (containClause5 2 8) := by decide
  rw [he]
  exact input_contain 2 8 (by decide) v hb
mask_input "13833|25108406941546723055343157692830665664409421777856138051584|260"
def inputClause13834 : CNF.NClause := [(2,true),(9,true),(195,false)]
theorem inputList13834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13834 = (containClause5 2 9) := by decide
  rw [he]
  exact input_contain 2 9 (by decide) v hb
mask_input "13834|50216813883093446110686315385661331328818843555712276103168|516"
def inputClause13835 : CNF.NClause := [(2,true),(10,true),(196,false)]
theorem inputList13835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13835
  have he : decodeClause inputClause13835 = containClause5 2 10 := by decide
  rw [he]
  exact input_contain 2 10 (by decide) v hb
mask_input "13835|100433627766186892221372630771322662657637687111424552206336|1028"
def inputClause13836 : CNF.NClause := [(2,true),(11,true),(197,false)]
theorem inputList13836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13836 = (containClause5 2 11) := by decide
  rw [he]
  exact input_contain 2 11 (by decide) v hb
mask_input "13836|200867255532373784442745261542645325315275374222849104412672|2052"
def inputClause13837 : CNF.NClause := [(2,true),(12,true),(198,false)]
theorem inputList13837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13837 = (containClause5 2 12) := by decide
  rw [he]
  exact input_contain 2 12 (by decide) v hb
mask_input "13837|401734511064747568885490523085290650630550748445698208825344|4100"
def inputClause13838 : CNF.NClause := [(2,true),(13,true),(199,false)]
theorem inputList13838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13838 = (containClause5 2 13) := by decide
  rw [he]
  exact input_contain 2 13 (by decide) v hb
mask_input "13838|803469022129495137770981046170581301261101496891396417650688|8196"
def inputClause13839 : CNF.NClause := [(2,true),(14,true),(200,false)]
theorem inputList13839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13839 = (containClause5 2 14) := by decide
  rw [he]
  exact input_contain 2 14 (by decide) v hb
mask_input "13839|1606938044258990275541962092341162602522202993782792835301376|16388"
def inputClause13841 : CNF.NClause := [(2,true),(16,true),(202,false)]
theorem inputList13841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13841 = (containClause5 2 16) := by decide
  rw [he]
  exact input_contain 2 16 (by decide) v hb
mask_input "13841|6427752177035961102167848369364650410088811975131171341205504|65540"
def inputClause13843 : CNF.NClause := [(2,true),(18,true),(204,false)]
theorem inputList13843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13843 = (containClause5 2 18) := by decide
  rw [he]
  exact input_contain 2 18 (by decide) v hb
mask_input "13843|25711008708143844408671393477458601640355247900524685364822016|262148"
def inputClause13844 : CNF.NClause := [(2,true),(19,true),(205,false)]
theorem inputList13844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13844 = (containClause5 2 19) := by decide
  rw [he]
  exact input_contain 2 19 (by decide) v hb
mask_input "13844|51422017416287688817342786954917203280710495801049370729644032|524292"
def inputClause13846 : CNF.NClause := [(2,true),(21,true),(207,false)]
theorem inputList13846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13846 = (containClause5 2 21) := by decide
  rw [he]
  exact input_contain 2 21 (by decide) v hb
mask_input "13846|205688069665150755269371147819668813122841983204197482918576128|2097156"
def inputClause13847 : CNF.NClause := [(2,true),(22,true),(208,false)]
theorem inputList13847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13847 = (containClause5 2 22) := by decide
  rw [he]
  exact input_contain 2 22 (by decide) v hb
mask_input "13847|411376139330301510538742295639337626245683966408394965837152256|4194308"
def inputClause13849 : CNF.NClause := [(2,true),(24,true),(210,false)]
theorem inputList13849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13849 = (containClause5 2 24) := by decide
  rw [he]
  exact input_contain 2 24 (by decide) v hb
mask_input "13849|1645504557321206042154969182557350504982735865633579863348609024|16777220"
def inputClause13851 : CNF.NClause := [(2,true),(26,true),(212,false)]
theorem inputList13851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13851 = (containClause5 2 26) := by decide
  rw [he]
  exact input_contain 2 26 (by decide) v hb
mask_input "13851|6582018229284824168619876730229402019930943462534319453394436096|67108868"
def inputClause13854 : CNF.NClause := [(2,true),(29,true),(215,false)]
theorem inputList13854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13854 = (containClause5 2 29) := by decide
  rw [he]
  exact input_contain 2 29 (by decide) v hb
mask_input "13854|52656145834278593348959013841835216159447547700274555627155488768|536870916"
def inputClause13917 : CNF.NClause := [(5,true),(1,true),(280,false)]
theorem inputList13917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13917
  have he : decodeClause inputClause13917 = containClause5 5 1 := by decide
  rw [he]
  exact input_contain 5 1 (by decide) v hb
mask_input "13917|1942668892225729070919461906823518906642406839052139521251812409738904285205208498176|34"
def inputClause13918 : CNF.NClause := [(5,true),(2,true),(281,false)]
theorem inputList13918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13918
  have he : decodeClause inputClause13918 = containClause5 5 2 := by decide
  rw [he]
  exact input_contain 5 2 (by decide) v hb
mask_input "13918|3885337784451458141838923813647037813284813678104279042503624819477808570410416996352|36"
def inputClause13921 : CNF.NClause := [(5,true),(6,true),(285,false)]
theorem inputList13921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13921
  have he : decodeClause inputClause13921 = containClause5 5 6 := by decide
  rw [he]
  exact input_contain 5 6 (by decide) v hb
mask_input "13921|62165404551223330269422781018352605012557018849668464680057997111644937126566671941632|96"
def inputClause13922 : CNF.NClause := [(5,true),(7,true),(286,false)]
theorem inputList13922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13922 = (containClause5 5 7) := by decide
  rw [he]
  exact input_contain 5 7 (by decide) v hb
mask_input "13922|124330809102446660538845562036705210025114037699336929360115994223289874253133343883264|160"
def inputClause13923 : CNF.NClause := [(5,true),(8,true),(287,false)]
theorem inputList13923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13923
  have he : decodeClause inputClause13923 = containClause5 5 8 := by decide
  rw [he]
  exact input_contain 5 8 (by decide) v hb
mask_input "13923|248661618204893321077691124073410420050228075398673858720231988446579748506266687766528|288"
def inputClause13924 : CNF.NClause := [(5,true),(9,true),(288,false)]
theorem inputList13924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13924
  have he : decodeClause inputClause13924 = containClause5 5 9 := by decide
  rw [he]
  exact input_contain 5 9 (by decide) v hb
mask_input "13924|497323236409786642155382248146820840100456150797347717440463976893159497012533375533056|544"
def inputClause13925 : CNF.NClause := [(5,true),(10,true),(289,false)]
theorem inputList13925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13925
  have he : decodeClause inputClause13925 = containClause5 5 10 := by decide
  rw [he]
  exact input_contain 5 10 (by decide) v hb
mask_input "13925|994646472819573284310764496293641680200912301594695434880927953786318994025066751066112|1056"
def inputClause13926 : CNF.NClause := [(5,true),(11,true),(290,false)]
theorem inputList13926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13926 = (containClause5 5 11) := by decide
  rw [he]
  exact input_contain 5 11 (by decide) v hb
mask_input "13926|1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224|2080"
def inputClause13927 : CNF.NClause := [(5,true),(12,true),(291,false)]
theorem inputList13927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13927
  have he : decodeClause inputClause13927 = containClause5 5 12 := by decide
  rw [he]
  exact input_contain 5 12 (by decide) v hb
mask_input "13927|3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448|4128"
end Percolation.MaskChain
