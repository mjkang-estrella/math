import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7494 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7494 (by decide) v hb
mask_input "7494|39063420446214099786792960|618970609938500496289431552"
def inputClause7495 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7495 (by decide) v hb
mask_input "7495|39063415834528081493622784|618970614550186514582601728"
def inputClause7496 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7496 (by decide) v hb
mask_input "7496|39063415834528081359405056|618970614550186514716819456"
def inputClause7497 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7497 (by decide) v hb
mask_input "7497|38988452878298544303243264|619045577506416051772981248"
def inputClause7498 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7498 (by decide) v hb
mask_input "7498|38988452878298544169025536|619045577506416051907198976"
def inputClause7499 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7499 (by decide) v hb
mask_input "7499|38988448266612525875855360|619045582118102070200369152"
def inputClause7500 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7500 (by decide) v hb
mask_input "7500|38988448266612525741637632|619045582118102070334586880"
def inputClause7501 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7501 (by decide) v hb
mask_input "7501|38987862582488185597591552|619046167802226410478632960"
def inputClause7502 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7502 (by decide) v hb
mask_input "7502|38987862582488185463373824|619046167802226410612850688"
def inputClause7503 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7503 (by decide) v hb
mask_input "7503|38987857970802167170203648|619046172413912428906020864"
def inputClause7504 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inputList7504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7504 (by decide) v hb
mask_input "7504|38987857970802167035985920|619046172413912429040238592"
def inputClause7505 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7505 (by decide) v hb
mask_input "7505|38761779287120801332985856|619272251097593794743238656"
def inputClause7506 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7506 (by decide) v hb
mask_input "7506|38761779287120801198768128|619272251097593794877456384"
def inputClause7507 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7507 (by decide) v hb
mask_input "7507|38761774675434782905597952|619272255709279813170626560"
def inputClause7508 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7508 (by decide) v hb
mask_input "7508|38761774675434782771380224|619272255709279813304844288"
def inputClause7509 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7509 (by decide) v hb
mask_input "7509|38761188991310442627334144|619272841393404153448890368"
def inputClause7510 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7510 (by decide) v hb
mask_input "7510|38761188991310442493116416|619272841393404153583108096"
def inputClause7511 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7511 (by decide) v hb
mask_input "7511|38761184379624424199946240|619272846005090171876278272"
def inputClause7512 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inputList7512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7512 (by decide) v hb
mask_input "7512|38761184379624424065728512|619272846005090172010496000"
def inputClause7513 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inputList7513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7513 (by decide) v hb
mask_input "7513|38686221423394887009566720|619347808961319709066657792"
def inputClause7514 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inputList7514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7514 (by decide) v hb
mask_input "7514|38686221423394886875348992|619347808961319709200875520"
def inputClause7515 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inputList7515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7515 (by decide) v hb
mask_input "7515|38686216811708868582178816|619347813573005727494045696"
def inputClause7516 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inputList7516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7516 (by decide) v hb
mask_input "7516|38686216811708868447961088|619347813573005727628263424"
def inputClause7517 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,false),(89,true)]
theorem inputList7517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7517 (by decide) v hb
mask_input "7517|38685631127584528303915008|619348399257130067772309504"
def inputClause7518 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,false),(89,true)]
theorem inputList7518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7518 (by decide) v hb
mask_input "7518|38685631127584528169697280|619348399257130067906527232"
def inputClause7520 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,false),(89,true)]
theorem inputList7520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7520 (by decide) v hb
mask_input "7520|38685626515898509742309376|619348403868816086333915136"
def inputClause7521 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7521 (by decide) v hb
mask_input "7521|378384514356325036064768|657655645870358271040159744"
def inputClause7522 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7522 (by decide) v hb
mask_input "7522|378384514356324901847040|657655645870358271174377472"
def inputClause7523 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7523 (by decide) v hb
mask_input "7523|378379902670306608676864|657655650482044289467547648"
def inputClause7524 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7524 (by decide) v hb
mask_input "7524|378379902670306474459136|657655650482044289601765376"
def inputClause7525 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7525 (by decide) v hb
mask_input "7525|377794218545966330413056|657656236166168629745811456"
def inputClause7526 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7526 (by decide) v hb
mask_input "7526|377794218545966196195328|657656236166168629880029184"
def inputClause7527 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7527 (by decide) v hb
mask_input "7527|377789606859947903025152|657656240777854648173199360"
def inputClause7528 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inputList7528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7528 (by decide) v hb
mask_input "7528|377789606859947768807424|657656240777854648307417088"
def inputClause7529 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7529 (by decide) v hb
mask_input "7529|302826650630410712645632|657731203734084185363578880"
def inputClause7530 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7530 (by decide) v hb
mask_input "7530|302826650630410578427904|657731203734084185497796608"
def inputClause7531 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7531 (by decide) v hb
mask_input "7531|302822038944392285257728|657731208345770203790966784"
def inputClause7532 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7532 (by decide) v hb
mask_input "7532|302822038944392151040000|657731208345770203925184512"
def inputClause7533 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7533 (by decide) v hb
mask_input "7533|302236354820052006993920|657731794029894544069230592"
def inputClause7534 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7534 (by decide) v hb
mask_input "7534|302236354820051872776192|657731794029894544203448320"
end Percolation.MaskChain
