import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7912 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,true),(87,true)]
theorem inputList7912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7912 (by decide) v hb
mask_input "7912|155840399777707505745920|159578360374769660238757888"
def inputClause7914 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,true),(87,true)]
theorem inputList7914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7914 (by decide) v hb
mask_input "7914|151270218933445964333056|159582930555613921780170752"
def inputClause7916 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,true),(87,true)]
theorem inputList7916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7916 (by decide) v hb
mask_input "7916|151265607247427536945152|159582935167299940207558656"
def inputClause7918 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,true),(87,true)]
theorem inputList7918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7918 (by decide) v hb
mask_input "7918|151122644980856287920128|159583078129566511456583680"
def inputClause7920 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,true),(87,true)]
theorem inputList7920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7920 (by decide) v hb
mask_input "7920|151118033294837860532224|159583082741252529883971584"
def inputClause7922 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,true),(87,true)]
theorem inputList7922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7922 (by decide) v hb
mask_input "7922|4876857964486962708480|159729323916582880781795328"
def inputClause7924 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,true),(87,true)]
theorem inputList7924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7924 (by decide) v hb
mask_input "7924|4872246278468535320576|159729328528268899209183232"
def inputClause7926 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,true),(87,true)]
theorem inputList7926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7926 (by decide) v hb
mask_input "7926|4729284011897286295552|159729471490535470458208256"
def inputClause7928 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,true),(87,true)]
theorem inputList7928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7928 (by decide) v hb
mask_input "7928|4724672325878858907648|159729476102221488885596160"
def inputClause7930 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,true),(87,true)]
theorem inputList7930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7930 (by decide) v hb
mask_input "7930|154491481617317494784|159734046283065750427009024"
def inputClause7932 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,true),(87,true)]
theorem inputList7932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7932 (by decide) v hb
mask_input "7932|149879795598890106880|159734050894751768854396928"
def inputClause7934 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,true),(87,true)]
theorem inputList7934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7934 (by decide) v hb
mask_input "7934|6917529027641081856|159734193857018340103421952"
def inputClause7936 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,true),(87,true)]
theorem inputList7936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7936 (by decide) v hb
mask_input "7936|2305843009213693952|159734198468704358530809856"
def inputClause7969 : CNF.NClause := [(149,true),(150,true),(151,true),(152,true),(153,false),(154,true)]
theorem inputList7969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) inputClause7969 (by decide) v hb
mask_input "7969|11417981541647679048466287755595961091061972992|33540320778590057204869720282063135704994545664"
def inputClause7970 : CNF.NClause := [(149,true),(150,true),(151,true),(152,false),(153,true),(154,true)]
theorem inputList7970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) inputClause7970 (by decide) v hb
mask_input "7970|5708990770823839524233143877797980545530986496|39249311549413896729102864159861116250525532160"
def inputClause7971 : CNF.NClause := [(149,true),(150,true),(151,false),(152,true),(153,true),(154,true)]
theorem inputList7971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) inputClause7971 (by decide) v hb
mask_input "7971|2854495385411919762116571938898990272765493248|42103806934825816491219436098760106523291025408"
def inputClause7972 : CNF.NClause := [(149,true),(150,false),(151,true),(152,true),(153,true),(154,true)]
theorem inputList7972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) inputClause7972 (by decide) v hb
mask_input "7972|1427247692705959881058285969449495136382746624|43531054627531776372277722068209601659673772032"
def inputClause7975 : CNF.NClause := [(128,true),(133,true),(138,true),(143,true),(148,false),(149,true)]
theorem inputList7975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) inputClause7975 (by decide) v hb
mask_input "7975|356811923176489970264571492362373784095686656|725133897414080684055791630821127127943872512"
def inputClause7976 : CNF.NClause := [(128,true),(133,true),(138,true),(143,false),(148,true),(149,true)]
theorem inputList7976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) inputClause7976 (by decide) v hb
mask_input "7976|11150372599265311570767859136324180752990208|1070795447991305342749595264047176731286568960"
def inputClause7977 : CNF.NClause := [(128,true),(133,true),(138,false),(143,true),(148,true),(149,true)]
theorem inputList7977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) inputClause7977 (by decide) v hb
mask_input "7977|348449143727040986586495598010130648530944|1081597371446843613333776627585490781391028224"
def inputClause7978 : CNF.NClause := [(128,true),(133,false),(138,true),(143,true),(148,true),(149,true)]
theorem inputList7978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) inputClause7978 (by decide) v hb
mask_input "7978|10889035741470030830827987437816582766592|1081934931554829184289532295196063095456792576"
def inputClause7979 : CNF.NClause := [(128,false),(133,true),(138,true),(143,true),(148,true),(149,true)]
theorem inputList7979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) inputClause7979 (by decide) v hb
mask_input "7979|340282366920938463463374607431768211456|1081945480308203733381899659808893480271347712"
def inputClause7981 : CNF.NClause := [(126,true),(131,true),(136,true),(141,true),(146,false),(149,true)]
theorem inputList7981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) inputClause7981 (by decide) v hb
mask_input "7981|89202980794122492566142873090593446023921664|716501359118255126410805146248842458129498112"
def inputClause7982 : CNF.NClause := [(126,true),(131,true),(136,true),(141,false),(146,true),(149,true)]
theorem inputList7982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) inputClause7982 (by decide) v hb
mask_input "7982|2787593149816327892691964784081045188247552|802916746762561291084256054555354858965172224"
def inputClause7983 : CNF.NClause := [(126,true),(131,true),(136,false),(141,true),(146,true),(149,true)]
theorem inputList7983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) inputClause7983 (by decide) v hb
mask_input "7983|87112285931760246646623899502532662132736|805617227626445858730301395439933371491287040"
def inputClause7984 : CNF.NClause := [(126,true),(131,false),(136,true),(141,true),(146,true),(149,true)]
theorem inputList7984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) inputClause7984 (by decide) v hb
mask_input "7984|2722258935367507707706996859454145691648|805701617653442251469240312342576450007728128"
def inputClause7985 : CNF.NClause := [(126,false),(131,true),(136,true),(141,true),(146,true),(149,true)]
theorem inputList7985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) inputClause7985 (by decide) v hb
mask_input "7985|85070591730234615865843651857942052864|805704254841785888742332153495784046211366912"
def inputClause7987 : CNF.NClause := [(127,true),(132,true),(137,true),(142,true),(147,false),(149,true)]
theorem inputList7987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) inputClause7987 (by decide) v hb
mask_input "7987|178405961588244985132285746181186892047843328|719378871883530312292467307772937348067622912"
def inputClause7988 : CNF.NClause := [(127,true),(132,true),(137,true),(142,false),(147,true),(149,true)]
theorem inputList7988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) inputClause7988 (by decide) v hb
mask_input "7988|5575186299632655785383929568162090376495104|892209647172142641639369124385962149738971136"
def inputClause7989 : CNF.NClause := [(127,true),(132,true),(137,false),(142,true),(147,true),(149,true)]
theorem inputList7989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) inputClause7989 (by decide) v hb
mask_input "7989|174224571863520493293247799005065324265472|897610608899911776931459806155119174791200768"
def inputClause7990 : CNF.NClause := [(127,true),(132,false),(137,true),(142,true),(147,true),(149,true)]
theorem inputList7990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) inputClause7990 (by decide) v hb
mask_input "7990|5444517870735015415413993718908291383296|897779388953904562409337639960405331824082944"
def inputClause7991 : CNF.NClause := [(127,false),(132,true),(137,true),(142,true),(147,true),(149,true)]
theorem inputList7991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) inputClause7991 (by decide) v hb
mask_input "7991|170141183460469231731687303715884105728|897784663330591836955521322266820524231360512"
def inputClause7993 : CNF.NClause := [(125,true),(130,true),(135,true),(140,true),(145,false),(149,true)]
theorem inputList7993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) inputClause7993 (by decide) v hb
mask_input "7993|44601490397061246283071436545296723011960832|715062602735617533469974065486795013160435712"
def inputClause7994 : CNF.NClause := [(125,true),(130,true),(135,true),(140,false),(145,true),(149,true)]
theorem inputList7994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) inputClause7994 (by decide) v hb
mask_input "7994|1393796574908163946345982392040522594123776|758270296557770615806699519640051213578272768"
def inputClause7995 : CNF.NClause := [(125,true),(130,true),(135,false),(140,true),(145,true),(149,true)]
theorem inputList7995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) inputClause7995 (by decide) v hb
mask_input "7995|43556142965880123323311949751266331066368|759620536989712899629722190082340469841330176"
def inputClause7996 : CNF.NClause := [(125,true),(130,false),(135,true),(140,true),(145,true),(149,true)]
theorem inputList7996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) inputClause7996 (by decide) v hb
mask_input "7996|1361129467683753853853498429727072845824|759662732003211095999191648533662009099550720"
def inputClause7997 : CNF.NClause := [(125,false),(130,true),(135,true),(140,true),(145,true),(149,true)]
theorem inputList7997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) inputClause7997 (by decide) v hb
mask_input "7997|42535295865117307932921825928971026432|759664050597382914635737569110265807201370112"
def inputClause7999 : CNF.NClause := [(144,true),(145,true),(146,true),(147,true),(148,false),(154,true)]
theorem inputList7999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) inputClause7999 (by decide) v hb
mask_input "7999|356811923176489970264571492362373784095686656|23170474261273317444055611285281647604713652224"
def inputClause8000 : CNF.NClause := [(144,true),(145,true),(146,true),(147,false),(148,true),(154,true)]
theorem inputList8000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) inputClause8000 (by decide) v hb
mask_input "8000|178405961588244985132285746181186892047843328|23348880222861562429187897031462834496761495552"
def inputClause8001 : CNF.NClause := [(144,true),(145,true),(146,false),(147,true),(148,true),(154,true)]
theorem inputList8001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) inputClause8001 (by decide) v hb
mask_input "8001|89202980794122492566142873090593446023921664|23438083203655684921754039904553427942785417216"
end Percolation.MaskChain
