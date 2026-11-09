import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7608 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7608 (by decide) v hb
mask_input "7608|1237949484594806766492975104|21761849956370061251837952"
def inputClause7609 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7609 (by decide) v hb
mask_input "7609|1237941225065147763309674496|21770109486029064435138560"
def inputClause7610 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7610 (by decide) v hb
mask_input "7610|1237941225065147763041239040|21770109486029064703574016"
def inputClause7611 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7611 (by decide) v hb
mask_input "7611|1237941220453461744882286592|21770114097715082862526464"
def inputClause7612 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7612 (by decide) v hb
mask_input "7612|1237941220453461744613851136|21770114097715083130961920"
def inputClause7613 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7613 (by decide) v hb
mask_input "7613|1237940044473527045898371072|21771290077649781846441984"
def inputClause7614 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7614 (by decide) v hb
mask_input "7614|1237940044473527045629935616|21771290077649782114877440"
def inputClause7615 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7615 (by decide) v hb
mask_input "7615|1237940039861841027470983168|21771294689335800273829888"
def inputClause7616 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inputList7616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7616 (by decide) v hb
mask_input "7616|1237940039861841027202547712|21771294689335800542265344"
def inputClause7617 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7617 (by decide) v hb
mask_input "7617|21771295265796552845688832|1237940039285380274899124224"
def inputClause7618 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7618 (by decide) v hb
mask_input "7618|21771295265796552577253376|1237940039285380275167559680"
def inputClause7619 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7619 (by decide) v hb
mask_input "7619|21771290654110534418300928|1237940043897066293326512128"
def inputClause7621 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7621 (by decide) v hb
mask_input "7621|21770114674175835434385408|1237941219877000992310427648"
def inputClause7622 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7622 (by decide) v hb
mask_input "7622|21770114674175835165949952|1237941219877000992578863104"
def inputClause7623 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7623 (by decide) v hb
mask_input "7623|21770110062489817006997504|1237941224488687010737815552"
def inputClause7624 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7624 (by decide) v hb
mask_input "7624|21770110062489816738562048|1237941224488687011006251008"
def inputClause7625 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7625 (by decide) v hb
mask_input "7625|21761850532830813555261440|1237949484018346014189551616"
def inputClause7626 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7626 (by decide) v hb
mask_input "7626|21761850532830813286825984|1237949484018346014457987072"
def inputClause7627 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7627 (by decide) v hb
mask_input "7627|21761845921144795127873536|1237949488630032032616939520"
def inputClause7629 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7629 (by decide) v hb
mask_input "7629|21760669941210096143958016|1237950664609966731600855040"
def inputClause7630 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7630 (by decide) v hb
mask_input "7630|21760669941210095875522560|1237950664609966731869290496"
def inputClause7631 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7631 (by decide) v hb
mask_input "7631|21760665329524077716570112|1237950669221652750028242944"
def inputClause7632 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7632 (by decide) v hb
mask_input "7632|21760665329524077448134656|1237950669221652750296678400"
def inputClause7633 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7633 (by decide) v hb
mask_input "7633|19353443626567294496276480|1240357890924609533248536576"
def inputClause7634 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7634 (by decide) v hb
mask_input "7634|19353443626567294227841024|1240357890924609533516972032"
def inputClause7635 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7635 (by decide) v hb
mask_input "7635|19353439014881276068888576|1240357895536295551675924480"
def inputClause7637 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7637 (by decide) v hb
mask_input "7637|19352263034946577084973056|1240359071516230250659840000"
def inputClause7638 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7638 (by decide) v hb
mask_input "7638|19352263034946576816537600|1240359071516230250928275456"
def inputClause7639 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7639 (by decide) v hb
mask_input "7639|19352258423260558657585152|1240359076127916269087227904"
def inputClause7640 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7640 (by decide) v hb
mask_input "7640|19352258423260558389149696|1240359076127916269355663360"
def inputClause7641 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7641 (by decide) v hb
mask_input "7641|19343998893601555205849088|1240367335657575272538963968"
def inputClause7642 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7642 (by decide) v hb
mask_input "7642|19343998893601554937413632|1240367335657575272807399424"
def inputClause7643 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7643 (by decide) v hb
mask_input "7643|19343994281915536778461184|1240367340269261290966351872"
def inputClause7645 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7645 (by decide) v hb
mask_input "7645|19342818301980837794545664|1240368516249195989950267392"
def inputClause7646 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7646 (by decide) v hb
mask_input "7646|19342818301980837526110208|1240368516249195990218702848"
def inputClause7647 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7647 (by decide) v hb
mask_input "7647|19342813690294819367157760|1240368520860882008377655296"
def inputClause7648 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7648 (by decide) v hb
mask_input "7648|19342813690294819098722304|1240368520860882008646090752"
def inputClause7649 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7649 (by decide) v hb
mask_input "7649|2428482151962486050390016|1257282852399214341694423040"
def inputClause7650 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7650 (by decide) v hb
mask_input "7650|2428482151962485781954560|1257282852399214341962858496"
def inputClause7651 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7651 (by decide) v hb
mask_input "7651|2428477540276467623002112|1257282857010900360121810944"
end Percolation.MaskChain
