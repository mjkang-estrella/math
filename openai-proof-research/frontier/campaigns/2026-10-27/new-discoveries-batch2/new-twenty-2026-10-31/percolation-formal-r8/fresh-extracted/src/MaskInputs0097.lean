import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7011 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7011 (by decide) v hb
mask_input "7011|2436888697127725124550656|628641463093095318266314752"
def inputClause7012 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7012 (by decide) v hb
mask_input "7012|2436888697127725116162048|628641463093095318274703360"
def inputClause7013 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7013 (by decide) v hb
mask_input "7013|2436778016663282867240960|628641573773559760523624448"
def inputClause7014 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7014 (by decide) v hb
mask_input "7014|2436778016663282858852352|628641573773559760532013056"
def inputClause7015 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7015 (by decide) v hb
mask_input "7015|2436741123175135448137728|628641610667047907942727680"
def inputClause7016 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7016 (by decide) v hb
mask_input "7016|2436741123175135439749120|628641610667047907951116288"
def inputClause7017 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inputList7017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7017 (by decide) v hb
mask_input "7017|2418036124684393962799104|628660315665538649428066304"
def inputClause7018 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inputList7018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7018 (by decide) v hb
mask_input "7018|2418036124684393954410496|628660315665538649436454912"
def inputClause7019 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inputList7019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7019 (by decide) v hb
mask_input "7019|2417999231196246543695872|628660352559026796847169536"
def inputClause7020 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inputList7020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7020 (by decide) v hb
mask_input "7020|2417999231196246535307264|628660352559026796855558144"
def inputClause7021 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,true),(89,true)]
theorem inputList7021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7021 (by decide) v hb
mask_input "7021|2417888550731804286386176|628660463239491239104479232"
def inputClause7022 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,true),(89,true)]
theorem inputList7022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7022 (by decide) v hb
mask_input "7022|2417888550731804277997568|628660463239491239112867840"
def inputClause7024 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,true),(89,true)]
theorem inputList7024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7024 (by decide) v hb
mask_input "7024|2417851657243656858894336|628660500132979386531971072"
def inputClause7025 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7025 (by decide) v hb
mask_input "7025|19073951386614194241536|631059277838836429196623872"
def inputClause7026 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7026 (by decide) v hb
mask_input "7026|19073951386614185852928|631059277838836429205012480"
def inputClause7027 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7027 (by decide) v hb
mask_input "7027|19037057898466775138304|631059314732324576615727104"
def inputClause7028 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7028 (by decide) v hb
mask_input "7028|19037057898466766749696|631059314732324576624115712"
def inputClause7029 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7029 (by decide) v hb
mask_input "7029|18926377434024517828608|631059425412789018873036800"
def inputClause7030 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7030 (by decide) v hb
mask_input "7030|18926377434024509440000|631059425412789018881425408"
def inputClause7031 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7031 (by decide) v hb
mask_input "7031|18889483945877098725376|631059462306277166292140032"
def inputClause7032 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inputList7032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7032 (by decide) v hb
mask_input "7032|18889483945877090336768|631059462306277166300528640"
def inputClause7033 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,true),(89,true)]
theorem inputList7033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7033 (by decide) v hb
mask_input "7033|184485455135613386752|631078167304767907777478656"
def inputClause7034 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,true),(89,true)]
theorem inputList7034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7034 (by decide) v hb
mask_input "7034|184485455135604998144|631078167304767907785867264"
def inputClause7036 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,true),(89,true)]
theorem inputList7036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7036 (by decide) v hb
mask_input "7036|147591966988185894912|631078204198256055204970496"
def inputClause7037 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,true),(89,true)]
theorem inputList7037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7037 (by decide) v hb
mask_input "7037|36911502545936973824|631078314878720497453891584"
def inputClause7038 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,true),(89,true)]
theorem inputList7038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7038 (by decide) v hb
mask_input "7038|36911502545928585216|631078314878720497462280192"
def inputClause7040 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,true),(89,true)]
theorem inputList7040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7040 (by decide) v hb
mask_input "7040|18014398509481984|631078351772208644881383424"
def inputClause7043 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7043 (by decide) v hb
mask_input "7043|2496507522977916546803826688|9223372036854775808"
def inputClause7044 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7044 (by decide) v hb
mask_input "7044|2496507522977916546787049472|9223372036871553024"
def inputClause7045 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7045 (by decide) v hb
mask_input "7045|2496507384627335993982189568|147573952589676412928"
def inputClause7046 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7046 (by decide) v hb
mask_input "7046|2496507384627335993965412352|147573952589693190144"
def inputClause7047 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7047 (by decide) v hb
mask_input "7047|2496507375403963957127413760|156797324626531188736"
def inputClause7048 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7048 (by decide) v hb
mask_input "7048|2496507375403963957110636544|156797324626547965952"
def inputClause7049 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7049 (by decide) v hb
mask_input "7049|2496431974337562669335183360|75557863725914323419136"
def inputClause7050 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7050 (by decide) v hb
mask_input "7050|2496431974337562669318406144|75557863725914340196352"
def inputClause7051 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7051 (by decide) v hb
mask_input "7051|2496431965114190632480407552|75567087097951178194944"
def inputClause7052 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7052 (by decide) v hb
mask_input "7052|2496431965114190632463630336|75567087097951194972160"
def inputClause7053 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7053 (by decide) v hb
mask_input "7053|2496431826763610079658770432|75705437678503999832064"
def inputClause7054 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7054 (by decide) v hb
mask_input "7054|2496431826763610079641993216|75705437678504016609280"
def inputClause7055 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inputList7055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7055 (by decide) v hb
mask_input "7055|2496431817540238042803994624|75714661050540854607872"
end Percolation.MaskChain
