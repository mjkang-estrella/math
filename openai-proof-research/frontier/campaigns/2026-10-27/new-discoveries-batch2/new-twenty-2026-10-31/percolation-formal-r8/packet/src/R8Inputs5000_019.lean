import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4939 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4939 (by decide) v hb
mask_input "4939|6046990281314855574044800|618979482822399950449541120"
def inputClause4940 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4940 (by decide) v hb
mask_input "4940|6046990281314855574044672|618979482822399950449541248"
def inputClause4941 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4941 (by decide) v hb
mask_input "4941|6044647544817494460989568|618981825558897311562596352"
def inputClause4942 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4942 (by decide) v hb
mask_input "4942|6044647544817494460989440|618981825558897311562596480"
def inputClause4943 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4943 (by decide) v hb
mask_input "4943|6044629098073420751437952|618981844005641385272147968"
def inputClause4944 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4944 (by decide) v hb
mask_input "4944|6044629098073420751437824|618981844005641385272148096"
def inputClause4945 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4945 (by decide) v hb
mask_input "4945|4847527641410039399317632|620178945462304766624268288"
def inputClause4946 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4946 (by decide) v hb
mask_input "4946|4847527641410039399317504|620178945462304766624268416"
def inputClause4947 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4947 (by decide) v hb
mask_input "4947|4847509194665965689766016|620178963909048840333819904"
def inputClause4948 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4948 (by decide) v hb
mask_input "4948|4847509194665965689765888|620178963909048840333820032"
def inputClause4949 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4949 (by decide) v hb
mask_input "4949|4845166458168604576710784|620181306645546201446875136"
def inputClause4950 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4950 (by decide) v hb
mask_input "4950|4845166458168604576710656|620181306645546201446875264"
def inputClause4951 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4951 (by decide) v hb
mask_input "4951|4845148011424530867159168|620181325092290275156426752"
def inputClause4952 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inputList4952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4952 (by decide) v hb
mask_input "4952|4845148011424530867159040|620181325092290275156426880"
def inputClause4953 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4953 (by decide) v hb
mask_input "4953|4838082908444300108890240|620188390195270505914695680"
def inputClause4954 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4954 (by decide) v hb
mask_input "4954|4838082908444300108890112|620188390195270505914695808"
def inputClause4955 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4955 (by decide) v hb
mask_input "4955|4838064461700226399338624|620188408642014579624247296"
def inputClause4956 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4956 (by decide) v hb
mask_input "4956|4838064461700226399338496|620188408642014579624247424"
def inputClause4957 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4957 (by decide) v hb
mask_input "4957|4835721725202865286283392|620190751378511940737302528"
def inputClause4958 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4958 (by decide) v hb
mask_input "4958|4835721725202865286283264|620190751378511940737302656"
def inputClause4959 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4959 (by decide) v hb
mask_input "4959|4835703278458791576731776|620190769825256014446854144"
def inputClause4960 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inputList4960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4960 (by decide) v hb
mask_input "4960|4835703278458791576731648|620190769825256014446854272"
def inputClause4961 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4961 (by decide) v hb
mask_input "4961|1220750182566151875199104|623805722921148654148386816"
def inputClause4962 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4962 (by decide) v hb
mask_input "4962|1220750182566151875198976|623805722921148654148386944"
def inputClause4963 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4963 (by decide) v hb
mask_input "4963|1220731735822078165647488|623805741367892727857938432"
def inputClause4964 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4964 (by decide) v hb
mask_input "4964|1220731735822078165647360|623805741367892727857938560"
def inputClause4965 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4965 (by decide) v hb
mask_input "4965|1218388999324717052592256|623808084104390088970993664"
def inputClause4966 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4966 (by decide) v hb
mask_input "4966|1218388999324717052592128|623808084104390088970993792"
def inputClause4967 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4967 (by decide) v hb
mask_input "4967|1218370552580643343040640|623808102551134162680545280"
def inputClause4968 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inputList4968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4968 (by decide) v hb
mask_input "4968|1218370552580643343040512|623808102551134162680545408"
def inputClause4969 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4969 (by decide) v hb
mask_input "4969|1211305449600412584771712|623815167654114393438814208"
def inputClause4970 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4970 (by decide) v hb
mask_input "4970|1211305449600412584771584|623815167654114393438814336"
def inputClause4971 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4971 (by decide) v hb
mask_input "4971|1211287002856338875220096|623815186100858467148365824"
def inputClause4972 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4972 (by decide) v hb
mask_input "4972|1211287002856338875219968|623815186100858467148365952"
def inputClause4973 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4973 (by decide) v hb
mask_input "4973|1208944266358977762164864|623817528837355828261421056"
def inputClause4974 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4974 (by decide) v hb
mask_input "4974|1208944266358977762164736|623817528837355828261421184"
def inputClause4975 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4975 (by decide) v hb
mask_input "4975|1208925819614904052613248|623817547284099901970972672"
def inputClause4976 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inputList4976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4976 (by decide) v hb
mask_input "4976|1208925819614904052613120|623817547284099901970972800"
def inputClause4977 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inputList4977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4977 (by decide) v hb
mask_input "4977|11824362951522700492928|625014648740763283323092992"
def inputClause4978 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inputList4978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4978 (by decide) v hb
mask_input "4978|11824362951522700492800|625014648740763283323093120"
end Percolation.MaskChain
