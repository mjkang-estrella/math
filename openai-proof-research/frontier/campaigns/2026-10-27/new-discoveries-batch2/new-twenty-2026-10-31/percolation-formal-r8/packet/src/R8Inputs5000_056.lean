import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6836 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6836 (by decide) v hb
mask_input "6836|1237977965800203020991987712|77673502356983998188617728"
def inputClause6837 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6837 (by decide) v hb
mask_input "6837|1237977836672994505029320704|77673631484192514151284736"
def inputClause6838 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6838 (by decide) v hb
mask_input "6838|1237977836672994505025126400|77673631484192514155479040"
def inputClause6839 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6839 (by decide) v hb
mask_input "6839|1237977818226250431319769088|77673649930936587860836352"
def inputClause6840 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6840 (by decide) v hb
mask_input "6840|1237977818226250431315574784|77673649930936587865030656"
def inputClause6841 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6841 (by decide) v hb
mask_input "6841|1237940205315084137544024064|77711262842102881636581376"
def inputClause6843 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6843 (by decide) v hb
mask_input "6843|1237940186868340063834472448|77711281288846955346132992"
def inputClause6844 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6844 (by decide) v hb
mask_input "6844|1237940186868340063830278144|77711281288846955350327296"
def inputClause6845 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6845 (by decide) v hb
mask_input "6845|1237940057741131547867611136|77711410416055471312994304"
def inputClause6846 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6846 (by decide) v hb
mask_input "6846|1237940057741131547863416832|77711410416055471317188608"
def inputClause6847 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6847 (by decide) v hb
mask_input "6847|1237940039294387474158059520|77711428862799545022545920"
def inputClause6848 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6848 (by decide) v hb
mask_input "6848|1237940039294387474153865216|77711428862799545026740224"
def inputClause6849 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6849 (by decide) v hb
mask_input "6849|77711428871806744281481216|1237940039285380274899124224"
def inputClause6851 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6851 (by decide) v hb
mask_input "6851|77711410425062670571929600|1237940057732124348608675840"
def inputClause6852 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6852 (by decide) v hb
mask_input "6852|77711410425062670567735296|1237940057732124348612870144"
def inputClause6853 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6853 (by decide) v hb
mask_input "6853|77711281297854154605068288|1237940186859332864575537152"
def inputClause6854 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6854 (by decide) v hb
mask_input "6854|77711281297854154600873984|1237940186859332864579731456"
def inputClause6855 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6855 (by decide) v hb
mask_input "6855|77711262851110080895516672|1237940205306076938285088768"
def inputClause6856 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6856 (by decide) v hb
mask_input "6856|77711262851110080891322368|1237940205306076938289283072"
def inputClause6857 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6857 (by decide) v hb
mask_input "6857|77673649939943787119771648|1237977818217243232060833792"
def inputClause6859 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6859 (by decide) v hb
mask_input "6859|77673631493199713410220032|1237977836663987305770385408"
def inputClause6860 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6860 (by decide) v hb
mask_input "6860|77673631493199713406025728|1237977836663987305774579712"
def inputClause6861 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6861 (by decide) v hb
mask_input "6861|77673502365991197443358720|1237977965791195821737246720"
def inputClause6862 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6862 (by decide) v hb
mask_input "6862|77673502365991197439164416|1237977965791195821741441024"
def inputClause6863 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6863 (by decide) v hb
mask_input "6863|77673483919247123733807104|1237977984237939895446798336"
def inputClause6864 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6864 (by decide) v hb
mask_input "6864|77673483919247123729612800|1237977984237939895450992640"
def inputClause6865 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6865 (by decide) v hb
mask_input "6865|77409197416903086987804672|1238242270740283932192800768"
def inputClause6867 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6867 (by decide) v hb
mask_input "6867|77409178970159013278253056|1238242289187028005902352384"
def inputClause6868 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6868 (by decide) v hb
mask_input "6868|77409178970159013274058752|1238242289187028005906546688"
def inputClause6869 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6869 (by decide) v hb
mask_input "6869|77409049842950497311391744|1238242418314236521869213696"
def inputClause6870 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6870 (by decide) v hb
mask_input "6870|77409049842950497307197440|1238242418314236521873408000"
def inputClause6871 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6871 (by decide) v hb
mask_input "6871|77409031396206423601840128|1238242436760980595578765312"
def inputClause6872 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6872 (by decide) v hb
mask_input "6872|77409031396206423597645824|1238242436760980595582959616"
def inputClause6873 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6873 (by decide) v hb
mask_input "6873|77371418485040129826095104|1238280049672146889354510336"
def inputClause6875 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6875 (by decide) v hb
mask_input "6875|77371400038296056116543488|1238280068118890963064061952"
def inputClause6876 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6876 (by decide) v hb
mask_input "6876|77371400038296056112349184|1238280068118890963068256256"
def inputClause6877 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6877 (by decide) v hb
mask_input "6877|77371270911087540149682176|1238280197246099479030923264"
def inputClause6878 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6878 (by decide) v hb
mask_input "6878|77371270911087540145487872|1238280197246099479035117568"
def inputClause6879 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6879 (by decide) v hb
mask_input "6879|77371252464343466440130560|1238280215692843552740474880"
def inputClause6880 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6880 (by decide) v hb
mask_input "6880|77371252464343466435936256|1238280215692843552744669184"
end Percolation.MaskChain
