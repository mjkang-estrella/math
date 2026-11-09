import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3992 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,false),(92,false)]
theorem inputList3992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3992 (by decide) v hb
mask_input "3992|8046610255354971788991791104|1702167554017397877986295809"
def inputClause3994 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,false),(92,false)]
theorem inputList3994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3994 (by decide) v hb
mask_input "3994|7891867750444299254629400576|1856910058928070412348686337"
def inputClause3996 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,false),(92,false)]
theorem inputList3996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3996 (by decide) v hb
mask_input "3996|7737125245533626720267010048|2011652563838742946711076865"
def inputClause3998 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,false),(92,false)]
theorem inputList3998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3998 (by decide) v hb
mask_input "3998|7582382740622954185904619520|2166395068749415481073467393"
def inputClause4000 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,false),(92,false)]
theorem inputList4000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4000 (by decide) v hb
mask_input "4000|7427640235712281651542228992|2321137573660088015435857921"
def inputClause4002 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,true),(92,false)]
theorem inputList4002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4002 (by decide) v hb
mask_input "4002|7272897730801609117179838464|2475880078570760549798248449"
def inputClause4004 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,true),(92,false)]
theorem inputList4004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4004 (by decide) v hb
mask_input "4004|7118155225890936582817447936|2630622583481433084160638977"
def inputClause4006 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,true),(92,false)]
theorem inputList4006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4006 (by decide) v hb
mask_input "4006|6963412720980264048455057408|2785365088392105618523029505"
def inputClause4008 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,true),(92,false)]
theorem inputList4008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4008 (by decide) v hb
mask_input "4008|6808670216069591514092666880|2940107593302778152885420033"
def inputClause4010 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,true),(92,false)]
theorem inputList4010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4010 (by decide) v hb
mask_input "4010|6653927711158918979730276352|3094850098213450687247810561"
def inputClause4012 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,true),(92,false)]
theorem inputList4012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4012 (by decide) v hb
mask_input "4012|6499185206248246445367885824|3249592603124123221610201089"
def inputClause4014 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,true),(92,false)]
theorem inputList4014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4014 (by decide) v hb
mask_input "4014|6344442701337573911005495296|3404335108034795755972591617"
def inputClause4016 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,true),(92,false)]
theorem inputList4016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4016 (by decide) v hb
mask_input "4016|6189700196426901376643104768|3559077612945468290334982145"
def inputClause4018 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,true),(92,false)]
theorem inputList4018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4018 (by decide) v hb
mask_input "4018|6034957691516228842280714240|3713820117856140824697372673"
def inputClause4020 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,true),(92,false)]
theorem inputList4020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4020 (by decide) v hb
mask_input "4020|5880215186605556307918323712|3868562622766813359059763201"
def inputClause4022 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,true),(92,false)]
theorem inputList4022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4022 (by decide) v hb
mask_input "4022|5725472681694883773555933184|4023305127677485893422153729"
def inputClause4024 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,true),(92,false)]
theorem inputList4024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4024 (by decide) v hb
mask_input "4024|5570730176784211239193542656|4178047632588158427784544257"
def inputClause4026 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,true),(92,false)]
theorem inputList4026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4026 (by decide) v hb
mask_input "4026|5415987671873538704831152128|4332790137498830962146934785"
def inputClause4028 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,true),(92,false)]
theorem inputList4028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4028 (by decide) v hb
mask_input "4028|5261245166962866170468761600|4487532642409503496509325313"
def inputClause4030 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,true),(92,false)]
theorem inputList4030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4030 (by decide) v hb
mask_input "4030|5106502662052193636106371072|4642275147320176030871715841"
def inputClause4032 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,true),(92,false)]
theorem inputList4032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4032 (by decide) v hb
mask_input "4032|4951760157141521101743980544|4797017652230848565234106369"
def inputClause4034 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,false),(92,true)]
theorem inputList4034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4034 (by decide) v hb
mask_input "4034|4797017652230848567381590016|4951760157141521099596496897"
def inputClause4036 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,false),(92,true)]
theorem inputList4036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4036 (by decide) v hb
mask_input "4036|4642275147320176033019199488|5106502662052193633958887425"
def inputClause4038 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,false),(92,true)]
theorem inputList4038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4038 (by decide) v hb
mask_input "4038|4487532642409503498656808960|5261245166962866168321277953"
def inputClause4040 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,false),(92,true)]
theorem inputList4040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4040 (by decide) v hb
mask_input "4040|4332790137498830964294418432|5415987671873538702683668481"
def inputClause4042 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,false),(92,true)]
theorem inputList4042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4042 (by decide) v hb
mask_input "4042|4178047632588158429932027904|5570730176784211237046059009"
def inputClause4044 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,false),(92,true)]
theorem inputList4044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4044 (by decide) v hb
mask_input "4044|4023305127677485895569637376|5725472681694883771408449537"
def inputClause4046 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,false),(92,true)]
theorem inputList4046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4046 (by decide) v hb
mask_input "4046|3868562622766813361207246848|5880215186605556305770840065"
def inputClause4048 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,false),(92,true)]
theorem inputList4048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4048 (by decide) v hb
mask_input "4048|3713820117856140826844856320|6034957691516228840133230593"
def inputClause4050 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,false),(92,true)]
theorem inputList4050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4050 (by decide) v hb
mask_input "4050|3559077612945468292482465792|6189700196426901374495621121"
def inputClause4052 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,false),(92,true)]
theorem inputList4052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4052 (by decide) v hb
mask_input "4052|3404335108034795758120075264|6344442701337573908858011649"
def inputClause4054 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,false),(92,true)]
theorem inputList4054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4054 (by decide) v hb
mask_input "4054|3249592603124123223757684736|6499185206248246443220402177"
def inputClause4056 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,false),(92,true)]
theorem inputList4056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4056 (by decide) v hb
mask_input "4056|3094850098213450689395294208|6653927711158918977582792705"
def inputClause4058 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,false),(92,true)]
theorem inputList4058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4058 (by decide) v hb
mask_input "4058|2940107593302778155032903680|6808670216069591511945183233"
def inputClause4060 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,false),(92,true)]
theorem inputList4060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4060 (by decide) v hb
mask_input "4060|2785365088392105620670513152|6963412720980264046307573761"
def inputClause4062 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,false),(92,true)]
theorem inputList4062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4062 (by decide) v hb
mask_input "4062|2630622583481433086308122624|7118155225890936580669964289"
def inputClause4064 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,false),(92,true)]
theorem inputList4064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4064 (by decide) v hb
mask_input "4064|2475880078570760551945732096|7272897730801609115032354817"
def inputClause4066 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,true),(92,true)]
theorem inputList4066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4066 (by decide) v hb
mask_input "4066|2321137573660088017583341568|7427640235712281649394745345"
def inputClause4068 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,true),(92,true)]
theorem inputList4068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4068 (by decide) v hb
mask_input "4068|2166395068749415483220951040|7582382740622954183757135873"
def inputClause4070 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,true),(92,true)]
theorem inputList4070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause4070 (by decide) v hb
mask_input "4070|2011652563838742948858560512|7737125245533626718119526401"
end Percolation.MaskChain
