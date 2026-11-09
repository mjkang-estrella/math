import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7653 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7653 (by decide) v hb
mask_input "7653|2427301560341768639086592|1257284032990835059105726464"
def inputClause7654 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7654 (by decide) v hb
mask_input "7654|2427301560341768370651136|1257284032990835059374161920"
def inputClause7655 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7655 (by decide) v hb
mask_input "7655|2427296948655750211698688|1257284037602521077533114368"
def inputClause7656 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7656 (by decide) v hb
mask_input "7656|2427296948655749943263232|1257284037602521077801549824"
def inputClause7657 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7657 (by decide) v hb
mask_input "7657|2419037418996746759962624|1257292297132180080984850432"
def inputClause7658 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7658 (by decide) v hb
mask_input "7658|2419037418996746491527168|1257292297132180081253285888"
def inputClause7659 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7659 (by decide) v hb
mask_input "7659|2419032807310728332574720|1257292301743866099412238336"
def inputClause7661 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7661 (by decide) v hb
mask_input "7661|2417856827376029348659200|1257293477723800798396153856"
def inputClause7662 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7662 (by decide) v hb
mask_input "7662|2417856827376029080223744|1257293477723800798664589312"
def inputClause7663 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7663 (by decide) v hb
mask_input "7663|2417852215690010921271296|1257293482335486816823541760"
def inputClause7664 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7664 (by decide) v hb
mask_input "7664|2417852215690010652835840|1257293482335486817091977216"
def inputClause7665 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7665 (by decide) v hb
mask_input "7665|10630512733227700977664|1259700704038443600043835392"
def inputClause7666 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7666 (by decide) v hb
mask_input "7666|10630512733227432542208|1259700704038443600312270848"
def inputClause7667 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7667 (by decide) v hb
mask_input "7667|10625901047209273589760|1259700708650129618471223296"
def inputClause7669 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7669 (by decide) v hb
mask_input "7669|9449921112510289674240|1259701884630064317455138816"
def inputClause7670 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7670 (by decide) v hb
mask_input "7670|9449921112510021238784|1259701884630064317723574272"
def inputClause7671 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7671 (by decide) v hb
mask_input "7671|9445309426491862286336|1259701889241750335882526720"
def inputClause7672 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7672 (by decide) v hb
mask_input "7672|9445309426491593850880|1259701889241750336150962176"
def inputClause7673 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,true),(90,true)]
theorem inputList7673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7673 (by decide) v hb
mask_input "7673|1185779767488410550272|1259710148771409339334262784"
def inputClause7674 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,true),(90,true)]
theorem inputList7674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7674 (by decide) v hb
mask_input "7674|1185779767488142114816|1259710148771409339602698240"
def inputClause7678 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,true),(90,true)]
theorem inputList7678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7678 (by decide) v hb
mask_input "7678|5188146770730811392|1259711329363030057014001664"
def inputClause7680 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,true),(90,true)]
theorem inputList7680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7680 (by decide) v hb
mask_input "7680|576460752303423488|1259711333974716075441389568"
def inputClause7681 : CNF.NClause := [(60,true),(29,false),(62,false),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7681 (by decide) v hb
mask_input "7681|388084377321818641978621952|1152921504606846976"
def inputClause7697 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7697 (by decide) v hb
mask_input "7697|386875452655125517410762752|1208925819614629174706176"
def inputClause7938 : CNF.NClause := [(32,false),(97,false),(102,false),(107,false),(112,false),(117,false),(118,false)]
theorem inputList7938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 1) (final_mem 1) inputClause7938 (by decide) v hb
mask_input "7938|503820283613433434777130900140326912|0"
def inputClause7939 : CNF.NClause := [(33,false),(95,false),(100,false),(105,false),(110,false),(115,false),(118,false)]
theorem inputList7939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 2) (final_mem 2) inputClause7939 (by decide) v hb
mask_input "7939|375185320113030084863746556353839104|0"
def inputClause7940 : CNF.NClause := [(34,false),(96,false),(101,false),(106,false),(111,false),(116,false),(118,false)]
theorem inputList7940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 3) (final_mem 3) inputClause7940 (by decide) v hb
mask_input "7940|418063641279831201501541347637592064|0"
def inputClause7941 : CNF.NClause := [(35,false),(94,false),(99,false),(104,false),(109,false),(114,false),(118,false)]
theorem inputList7941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 4) (final_mem 4) inputClause7941 (by decide) v hb
mask_input "7941|353746159529629526544849190776733696|0"
def inputClause7942 : CNF.NClause := [(36,false),(113,false),(114,false),(115,false),(116,false),(117,false),(123,false)]
theorem inputList7942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 5) (final_mem 5) inputClause7942 (by decide) v hb
mask_input "7942|10955746371508486296199347323373879296|0"
def inputClause7943 : CNF.NClause := [(37,false),(97,false),(101,false),(105,false),(109,false),(113,false),(122,false)]
theorem inputList7943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 6) (final_mem 6) inputClause7943 (by decide) v hb
mask_input "7943|5327988872540782788654181758256807936|0"
def inputClause7944 : CNF.NClause := [(38,false),(95,false),(102,false),(104,false),(111,false),(113,false),(120,false)]
theorem inputList7944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 7) (final_mem 7) inputClause7944 (by decide) v hb
mask_input "7944|1342234130557338763695332306817384448|0"
def inputClause7945 : CNF.NClause := [(39,false),(96,false),(99,false),(107,false),(110,false),(113,false),(121,false)]
theorem inputList7945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 8) (final_mem 8) inputClause7945 (by decide) v hb
mask_input "7945|2670301631831826949714238206963089408|0"
def inputClause7946 : CNF.NClause := [(40,false),(94,false),(100,false),(106,false),(112,false),(113,false),(119,false)]
theorem inputList7946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 9) (final_mem 9) inputClause7946 (by decide) v hb
mask_input "7946|680273305564117882814677802733797376|0"
def inputClause7947 : CNF.NClause := [(41,false),(103,false),(104,false),(105,false),(106,false),(107,false),(123,false)]
theorem inputList7947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 10) (final_mem 10) inputClause7947 (by decide) v hb
mask_input "7947|10634138343628183584122029863660945408|0"
def inputClause7948 : CNF.NClause := [(42,false),(97,false),(100,false),(103,false),(111,false),(114,false),(121,false)]
theorem inputList7948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 11) (final_mem 11) inputClause7948 (by decide) v hb
mask_input "7948|2681832894744965552729294409505439744|0"
def inputClause7949 : CNF.NClause := [(43,false),(95,false),(99,false),(103,false),(112,false),(116,false),(122,false)]
theorem inputList7949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 12) (final_mem 12) inputClause7949 (by decide) v hb
mask_input "7949|5405191844378938758382336993560363008|0"
def inputClause7951 : CNF.NClause := [(45,false),(94,false),(101,false),(103,false),(110,false),(117,false),(120,false)]
theorem inputList7951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 14) (final_mem 14) inputClause7951 (by decide) v hb
mask_input "7951|1496692265785706974784050116687822848|0"
def inputClause7952 : CNF.NClause := [(46,false),(108,false),(109,false),(110,false),(111,false),(112,false),(123,false)]
theorem inputList7952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 15) (final_mem 15) inputClause7952 (by decide) v hb
mask_input "7952|10643884041442738211760804687624798208|0"
def inputClause7953 : CNF.NClause := [(47,false),(97,false),(99,false),(106,false),(108,false),(115,false),(120,false)]
theorem inputList7953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 16) (final_mem 16) inputClause7953 (by decide) v hb
mask_input "7953|1371172811126892669984046648867684352|0"
def inputClause7954 : CNF.NClause := [(48,false),(95,false),(101,false),(107,false),(108,false),(114,false),(119,false)]
theorem inputList7954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 17) (final_mem 17) inputClause7954 (by decide) v hb
mask_input "7954|685872538072366600647453514643013632|0"
end Percolation.MaskChain
