import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6928 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6928 (by decide) v hb
mask_input "6928|631059277856850827706105856|19073933372215684759552"
def inputClause6929 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6929 (by decide) v hb
mask_input "6929|628660500150993785041453056|2417851639229258349412352"
def inputClause6930 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6930 (by decide) v hb
mask_input "6930|628660500150993785033064448|2417851639229258357800960"
def inputClause6931 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6931 (by decide) v hb
mask_input "6931|628660463257505637622349824|2417888532717405768515584"
def inputClause6932 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6932 (by decide) v hb
mask_input "6932|628660463257505637613961216|2417888532717405776904192"
def inputClause6933 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6933 (by decide) v hb
mask_input "6933|628660352577041195365040128|2417999213181848025825280"
def inputClause6934 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6934 (by decide) v hb
mask_input "6934|628660352577041195356651520|2417999213181848034213888"
def inputClause6935 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6935 (by decide) v hb
mask_input "6935|628660315683553047945936896|2418036106669995444928512"
def inputClause6936 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inputList6936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6936 (by decide) v hb
mask_input "6936|628660315683553047937548288|2418036106669995453317120"
def inputClause6937 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6937 (by decide) v hb
mask_input "6937|628641610685062306460598272|2436741105160736930267136"
def inputClause6938 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6938 (by decide) v hb
mask_input "6938|628641610685062306452209664|2436741105160736938655744"
def inputClause6939 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6939 (by decide) v hb
mask_input "6939|628641573791574159041495040|2436777998648884349370368"
def inputClause6940 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6940 (by decide) v hb
mask_input "6940|628641573791574159033106432|2436777998648884357758976"
def inputClause6941 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6941 (by decide) v hb
mask_input "6941|628641463111109716784185344|2436888679113326606680064"
def inputClause6942 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6942 (by decide) v hb
mask_input "6942|628641463111109716775796736|2436888679113326615068672"
def inputClause6943 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6943 (by decide) v hb
mask_input "6943|628641426217621569365082112|2436925572601474025783296"
def inputClause6944 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inputList6944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6944 (by decide) v hb
mask_input "6944|628641426217621569356693504|2436925572601474034171904"
def inputClause6945 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6945 (by decide) v hb
mask_input "6945|621406945233306009993216000|9671406556917033397649408"
def inputClause6946 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6946 (by decide) v hb
mask_input "6946|621406945233306009984827392|9671406556917033406038016"
def inputClause6947 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6947 (by decide) v hb
mask_input "6947|621406908339817862574112768|9671443450405180816752640"
def inputClause6948 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6948 (by decide) v hb
mask_input "6948|621406908339817862565724160|9671443450405180825141248"
def inputClause6949 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6949 (by decide) v hb
mask_input "6949|621406797659353420316803072|9671554130869623074062336"
def inputClause6950 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6950 (by decide) v hb
mask_input "6950|621406797659353420308414464|9671554130869623082450944"
def inputClause6951 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6951 (by decide) v hb
mask_input "6951|621406760765865272897699840|9671591024357770493165568"
def inputClause6952 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inputList6952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6952 (by decide) v hb
mask_input "6952|621406760765865272889311232|9671591024357770501554176"
def inputClause6953 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6953 (by decide) v hb
mask_input "6953|621388055767374531412361216|9690296022848511978504192"
def inputClause6954 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6954 (by decide) v hb
mask_input "6954|621388055767374531403972608|9690296022848511986892800"
def inputClause6955 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6955 (by decide) v hb
mask_input "6955|621388018873886383993257984|9690332916336659397607424"
def inputClause6956 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6956 (by decide) v hb
mask_input "6956|621388018873886383984869376|9690332916336659405996032"
def inputClause6957 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6957 (by decide) v hb
mask_input "6957|621387908193421941735948288|9690443596801101654917120"
def inputClause6958 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6958 (by decide) v hb
mask_input "6958|621387908193421941727559680|9690443596801101663305728"
def inputClause6959 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6959 (by decide) v hb
mask_input "6959|621387871299933794316845056|9690480490289249074020352"
def inputClause6960 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inputList6960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6960 (by decide) v hb
mask_input "6960|621387871299933794308456448|9690480490289249082408960"
def inputClause6961 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inputList6961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6961 (by decide) v hb
mask_input "6961|618989093594076751643803648|12089258196146291747061760"
def inputClause6962 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inputList6962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6962 (by decide) v hb
mask_input "6962|618989093594076751635415040|12089258196146291755450368"
def inputClause6963 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inputList6963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6963 (by decide) v hb
mask_input "6963|618989056700588604224700416|12089295089634439166164992"
def inputClause6964 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inputList6964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6964 (by decide) v hb
mask_input "6964|618989056700588604216311808|12089295089634439174553600"
def inputClause6965 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,true),(89,false)]
theorem inputList6965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6965 (by decide) v hb
mask_input "6965|618988946020124161967390720|12089405770098881423474688"
def inputClause6966 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,true),(89,false)]
theorem inputList6966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6966 (by decide) v hb
mask_input "6966|618988946020124161959002112|12089405770098881431863296"
def inputClause6968 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,true),(89,false)]
theorem inputList6968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6968 (by decide) v hb
mask_input "6968|618988909126636014539898880|12089442663587028850966528"
end Percolation.MaskChain
