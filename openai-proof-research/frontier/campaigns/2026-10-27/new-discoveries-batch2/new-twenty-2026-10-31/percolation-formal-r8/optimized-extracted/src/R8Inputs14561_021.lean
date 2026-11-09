import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause13928 : CNF.NClause := [(5,true),(13,true),(292,false)]
theorem inputList13928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13928
  have he : decodeClause inputClause13928 = containClause5 5 13 := by decide
  rw [he]
  exact input_contain 5 13 (by decide) v hb
mask_input "13928|7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896|8224"
def inputClause13929 : CNF.NClause := [(5,true),(14,true),(293,false)]
theorem inputList13929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13929 = (containClause5 5 14) := by decide
  rw [he]
  exact input_contain 5 14 (by decide) v hb
mask_input "13929|15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792|16416"
def inputClause13931 : CNF.NClause := [(5,true),(16,true),(295,false)]
theorem inputList13931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13931 = (containClause5 5 16) := by decide
  rw [he]
  exact input_contain 5 16 (by decide) v hb
mask_input "13931|63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168|65568"
def inputClause13933 : CNF.NClause := [(5,true),(18,true),(297,false)]
theorem inputList13933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13933
  have he : decodeClause inputClause13933 = containClause5 5 18 := by decide
  rw [he]
  exact input_contain 5 18 (by decide) v hb
mask_input "13933|254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672|262176"
def inputClause13934 : CNF.NClause := [(5,true),(19,true),(298,false)]
theorem inputList13934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13934
  have he : decodeClause inputClause13934 = containClause5 5 19 := by decide
  rw [he]
  exact input_contain 5 19 (by decide) v hb
mask_input "13934|509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344|524320"
def inputClause13936 : CNF.NClause := [(5,true),(21,true),(300,false)]
theorem inputList13936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13936
  have he : decodeClause inputClause13936 = containClause5 5 21 := by decide
  rw [he]
  exact input_contain 5 21 (by decide) v hb
mask_input "13936|2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376|2097184"
def inputClause13937 : CNF.NClause := [(5,true),(22,true),(301,false)]
theorem inputList13937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13937 = (containClause5 5 22) := by decide
  rw [he]
  exact input_contain 5 22 (by decide) v hb
mask_input "13937|4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752|4194336"
def inputClause13939 : CNF.NClause := [(5,true),(24,true),(303,false)]
theorem inputList13939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13939
  have he : decodeClause inputClause13939 = containClause5 5 24 := by decide
  rw [he]
  exact input_contain 5 24 (by decide) v hb
mask_input "13939|16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008|16777248"
def inputClause13941 : CNF.NClause := [(5,true),(26,true),(305,false)]
theorem inputList13941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13941
  have he : decodeClause inputClause13941 = containClause5 5 26 := by decide
  rw [he]
  exact input_contain 5 26 (by decide) v hb
mask_input "13941|65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032|67108896"
def inputClause13944 : CNF.NClause := [(5,true),(29,true),(308,false)]
theorem inputList13944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13944
  have he : decodeClause inputClause13944 = containClause5 5 29 := by decide
  rw [he]
  exact input_contain 5 29 (by decide) v hb
mask_input "13944|521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728256|536870944"
def inputClause13947 : CNF.NClause := [(6,true),(1,true),(311,false)]
theorem inputList13947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13947 = (containClause5 6 1) := by decide
  rw [he]
  exact input_contain 6 1 (by decide) v hb
mask_input "13947|4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048|66"
def inputClause13948 : CNF.NClause := [(6,true),(2,true),(312,false)]
theorem inputList13948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13948 = (containClause5 6 2) := by decide
  rw [he]
  exact input_contain 6 2 (by decide) v hb
mask_input "13948|8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096|68"
def inputClause13951 : CNF.NClause := [(6,true),(5,true),(315,false)]
theorem inputList13951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13951 = (containClause5 6 5) := by decide
  rw [he]
  exact input_contain 6 5 (by decide) v hb
mask_input "13951|66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768|96"
def inputClause13953 : CNF.NClause := [(6,true),(8,true),(318,false)]
theorem inputList13953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13953 = (containClause5 6 8) := by decide
  rw [he]
  exact input_contain 6 8 (by decide) v hb
mask_input "13953|533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144|320"
def inputClause13955 : CNF.NClause := [(6,true),(10,true),(320,false)]
theorem inputList13955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13955 = (containClause5 6 10) := by decide
  rw [he]
  exact input_contain 6 10 (by decide) v hb
mask_input "13955|2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576|1088"
def inputClause13956 : CNF.NClause := [(6,true),(11,true),(321,false)]
theorem inputList13956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13956 = (containClause5 6 11) := by decide
  rw [he]
  exact input_contain 6 11 (by decide) v hb
mask_input "13956|4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152|2112"
def inputClause13977 : CNF.NClause := [(7,true),(1,true),(342,false)]
theorem inputList13977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13977
  have he : decodeClause inputClause13977 = containClause5 7 1 := by decide
  rw [he]
  exact input_contain 7 1 (by decide) v hb
mask_input "13977|8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104|130"
def inputClause13978 : CNF.NClause := [(7,true),(2,true),(343,false)]
theorem inputList13978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13978 = (containClause5 7 2) := by decide
  rw [he]
  exact input_contain 7 2 (by decide) v hb
mask_input "13978|17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208|132"
def inputClause13981 : CNF.NClause := [(7,true),(5,true),(346,false)]
theorem inputList13981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13981 = (containClause5 7 5) := by decide
  rw [he]
  exact input_contain 7 5 (by decide) v hb
mask_input "13981|143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664|160"
def inputClause13983 : CNF.NClause := [(7,true),(8,true),(349,false)]
theorem inputList13983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13983 = (containClause5 7 8) := by decide
  rw [he]
  exact input_contain 7 8 (by decide) v hb
mask_input "13983|1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312|384"
def inputClause13985 : CNF.NClause := [(7,true),(10,true),(351,false)]
theorem inputList13985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13985 = (containClause5 7 10) := by decide
  rw [he]
  exact input_contain 7 10 (by decide) v hb
mask_input "13985|4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248|1152"
def inputClause13986 : CNF.NClause := [(7,true),(11,true),(352,false)]
theorem inputList13986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13986 = (containClause5 7 11) := by decide
  rw [he]
  exact input_contain 7 11 (by decide) v hb
mask_input "13986|9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496|2176"
def inputClause14007 : CNF.NClause := [(8,true),(1,true),(373,false)]
theorem inputList14007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14007 = (containClause5 8 1) := by decide
  rw [he]
  exact input_contain 8 1 (by decide) v hb
mask_input "14007|19239260838083241802870625048898248928261591440656956380834127638791856333738872368854622194768025215237611323392|258"
def inputClause14008 : CNF.NClause := [(8,true),(2,true),(374,false)]
theorem inputList14008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14008
  have he : decodeClause inputClause14008 = containClause5 8 2 := by decide
  rw [he]
  exact input_contain 8 2 (by decide) v hb
mask_input "14008|38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784|260"
def inputClause14011 : CNF.NClause := [(8,true),(5,true),(377,false)]
theorem inputList14011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14011
  have he : decodeClause inputClause14011 = containClause5 8 5 := by decide
  rw [he]
  exact input_contain 8 5 (by decide) v hb
mask_input "14011|307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272|288"
def inputClause14012 : CNF.NClause := [(8,true),(6,true),(378,false)]
theorem inputList14012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14012 = (containClause5 8 6) := by decide
  rw [he]
  exact input_contain 8 6 (by decide) v hb
mask_input "14012|615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544|320"
def inputClause14013 : CNF.NClause := [(8,true),(7,true),(379,false)]
theorem inputList14013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14013 = (containClause5 8 7) := by decide
  rw [he]
  exact input_contain 8 7 (by decide) v hb
mask_input "14013|1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088|384"
def inputClause14014 : CNF.NClause := [(8,true),(9,true),(381,false)]
theorem inputList14014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14014
  have he : decodeClause inputClause14014 = containClause5 8 9 := by decide
  rw [he]
  exact input_contain 8 9 (by decide) v hb
mask_input "14014|4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352|768"
def inputClause14015 : CNF.NClause := [(8,true),(10,true),(382,false)]
theorem inputList14015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14015 = (containClause5 8 10) := by decide
  rw [he]
  exact input_contain 8 10 (by decide) v hb
mask_input "14015|9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704|1280"
def inputClause14016 : CNF.NClause := [(8,true),(11,true),(383,false)]
theorem inputList14016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14016 = (containClause5 8 11) := by decide
  rw [he]
  exact input_contain 8 11 (by decide) v hb
mask_input "14016|19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408|2304"
def inputClause14017 : CNF.NClause := [(8,true),(12,true),(384,false)]
theorem inputList14017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14017 = (containClause5 8 12) := by decide
  rw [he]
  exact input_contain 8 12 (by decide) v hb
mask_input "14017|39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816|4352"
def inputClause14018 : CNF.NClause := [(8,true),(13,true),(385,false)]
theorem inputList14018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14018
  have he : decodeClause inputClause14018 = containClause5 8 13 := by decide
  rw [he]
  exact input_contain 8 13 (by decide) v hb
mask_input "14018|78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632|8448"
def inputClause14019 : CNF.NClause := [(8,true),(14,true),(386,false)]
theorem inputList14019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14019 = (containClause5 8 14) := by decide
  rw [he]
  exact input_contain 8 14 (by decide) v hb
mask_input "14019|157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264|16640"
def inputClause14021 : CNF.NClause := [(8,true),(16,true),(388,false)]
theorem inputList14021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14021
  have he : decodeClause inputClause14021 = containClause5 8 16 := by decide
  rw [he]
  exact input_contain 8 16 (by decide) v hb
mask_input "14021|630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056|65792"
def inputClause14023 : CNF.NClause := [(8,true),(18,true),(390,false)]
theorem inputList14023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14023 = (containClause5 8 18) := by decide
  rw [he]
  exact input_contain 8 18 (by decide) v hb
mask_input "14023|2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224|262400"
def inputClause14024 : CNF.NClause := [(8,true),(19,true),(391,false)]
theorem inputList14024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14024 = (containClause5 8 19) := by decide
  rw [he]
  exact input_contain 8 19 (by decide) v hb
mask_input "14024|5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448|524544"
def inputClause14026 : CNF.NClause := [(8,true),(21,true),(393,false)]
theorem inputList14026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14026
  have he : decodeClause inputClause14026 = containClause5 8 21 := by decide
  rw [he]
  exact input_contain 8 21 (by decide) v hb
mask_input "14026|20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792|2097408"
def inputClause14027 : CNF.NClause := [(8,true),(22,true),(394,false)]
theorem inputList14027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14027 = (containClause5 8 22) := by decide
  rw [he]
  exact input_contain 8 22 (by decide) v hb
mask_input "14027|40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584|4194560"
def inputClause14029 : CNF.NClause := [(8,true),(24,true),(396,false)]
theorem inputList14029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14029
  have he : decodeClause inputClause14029 = containClause5 8 24 := by decide
  rw [he]
  exact input_contain 8 24 (by decide) v hb
mask_input "14029|161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336|16777472"
def inputClause14031 : CNF.NClause := [(8,true),(26,true),(398,false)]
theorem inputList14031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14031 = (containClause5 8 26) := by decide
  rw [he]
  exact input_contain 8 26 (by decide) v hb
mask_input "14031|645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344|67109120"
end Percolation.MaskChain
