import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5780 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5780 (by decide) v hb
mask_input "5780|696347175056165176059363328|604472133179351442145280"
def inputClause5781 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5781 (by decide) v hb
mask_input "5781|696346003687916495502852096|605643501428031998656512"
def inputClause5783 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5783 (by decide) v hb
mask_input "5783|696345994464544458648076288|605652724800068853432320"
def inputClause5784 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5784 (by decide) v hb
mask_input "5784|696345994464544458648059904|605652724800068853448704"
def inputClause5785 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5785 (by decide) v hb
mask_input "5785|696342461913054343268941824|609185276290184232566784"
def inputClause5786 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5786 (by decide) v hb
mask_input "5786|696342461913054343268925440|609185276290184232583168"
def inputClause5787 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5787 (by decide) v hb
mask_input "5787|696342452689682306414166016|609194499662221087342592"
def inputClause5788 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5788 (by decide) v hb
mask_input "5788|696342452689682306414149632|609194499662221087358976"
def inputClause5789 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5789 (by decide) v hb
mask_input "5789|696341281321433625857638400|610365867910901643870208"
def inputClause5791 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5791 (by decide) v hb
mask_input "5791|696341272098061589002862592|610375091282938498646016"
def inputClause5792 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inputList5792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5792 (by decide) v hb
mask_input "5792|696341272098061589002846208|610375091282938498662400"
def inputClause5793 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5793 (by decide) v hb
mask_input "5793|619580394734008260320313344|77371252455336267181195264"
def inputClause5795 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5795 (by decide) v hb
mask_input "5795|619580385510636223465537536|77371261678708304035971072"
def inputClause5796 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5796 (by decide) v hb
mask_input "5796|619580385510636223465521152|77371261678708304035987456"
def inputClause5797 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5797 (by decide) v hb
mask_input "5797|619579214142387542909009920|77372433046956984592498688"
def inputClause5799 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5799 (by decide) v hb
mask_input "5799|619579204919015506054234112|77372442270329021447274496"
def inputClause5800 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5800 (by decide) v hb
mask_input "5800|619579204919015506054217728|77372442270329021447290880"
def inputClause5801 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5801 (by decide) v hb
mask_input "5801|619575672367525390675099648|77375974821819136826408960"
def inputClause5802 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5802 (by decide) v hb
mask_input "5802|619575672367525390675083264|77375974821819136826425344"
def inputClause5803 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5803 (by decide) v hb
mask_input "5803|619575663144153353820323840|77375984045191173681184768"
def inputClause5804 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5804 (by decide) v hb
mask_input "5804|619575663144153353820307456|77375984045191173681201152"
def inputClause5805 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5805 (by decide) v hb
mask_input "5805|619574491775904673263796224|77377155413439854237712384"
def inputClause5807 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5807 (by decide) v hb
mask_input "5807|619574482552532636409020416|77377164636811891092488192"
def inputClause5808 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5808 (by decide) v hb
mask_input "5808|619574482552532636409004032|77377164636811891092504576"
def inputClause5809 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5809 (by decide) v hb
mask_input "5809|618975931824200945732960256|77975715365143581768548352"
def inputClause5810 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5810 (by decide) v hb
mask_input "5810|618975931824200945732943872|77975715365143581768564736"
def inputClause5811 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5811 (by decide) v hb
mask_input "5811|618975922600828908878184448|77975724588515618623324160"
def inputClause5812 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5812 (by decide) v hb
mask_input "5812|618975922600828908878168064|77975724588515618623340544"
def inputClause5813 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5813 (by decide) v hb
mask_input "5813|618974751232580228321656832|77976895956764299179851776"
def inputClause5815 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5815 (by decide) v hb
mask_input "5815|618974742009208191466881024|77976905180136336034627584"
def inputClause5816 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5816 (by decide) v hb
mask_input "5816|618974742009208191466864640|77976905180136336034643968"
def inputClause5817 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5817 (by decide) v hb
mask_input "5817|618971209457718076087746560|77980437731626451413762048"
def inputClause5818 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5818 (by decide) v hb
mask_input "5818|618971209457718076087730176|77980437731626451413778432"
def inputClause5819 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5819 (by decide) v hb
mask_input "5819|618971200234346039232970752|77980446954998488268537856"
def inputClause5820 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5820 (by decide) v hb
mask_input "5820|618971200234346039232954368|77980446954998488268554240"
def inputClause5821 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5821 (by decide) v hb
mask_input "5821|618970028866097358676443136|77981618323247168825065472"
def inputClause5823 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5823 (by decide) v hb
mask_input "5823|618970019642725321821667328|77981627546619205679841280"
def inputClause5824 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5824 (by decide) v hb
mask_input "5824|618970019642725321821650944|77981627546619205679857664"
def inputClause5825 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5825 (by decide) v hb
mask_input "5825|77981627546654390051946496|618970019642690137449562112"
def inputClause5826 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5826 (by decide) v hb
mask_input "5826|77981627546654390051930112|618970019642690137449578496"
end Percolation.MaskChain
