import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6685 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6685 (by decide) v hb
mask_input "6685|348170709840493096783052800|614055216725643554193408"
def inputClause6687 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6687 (by decide) v hb
mask_input "6687|348170636053516801944846336|614129003701938392399872"
def inputClause6688 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6688 (by decide) v hb
mask_input "6688|348170636053516801942749184|614129003701938394497024"
def inputClause6689 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6689 (by decide) v hb
mask_input "6689|310099138829550606746648576|38685626227668133590597632"
def inputClause6690 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6690 (by decide) v hb
mask_input "6690|310099138829550606744551424|38685626227668133592694784"
def inputClause6691 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6691 (by decide) v hb
mask_input "6691|310099065042574311908442112|38685700014644428428804096"
def inputClause6692 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6692 (by decide) v hb
mask_input "6692|310099065042574311906344960|38685700014644428430901248"
def inputClause6693 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6693 (by decide) v hb
mask_input "6693|310098991255598017070235648|38685773801620723267010560"
def inputClause6695 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6695 (by decide) v hb
mask_input "6695|310098917468621722232029184|38685847588597018105217024"
def inputClause6696 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6696 (by decide) v hb
mask_input "6696|310098917468621722229932032|38685847588597018107314176"
def inputClause6697 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inputList6697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6697 (by decide) v hb
mask_input "6697|310089694096584867456221184|38695070960633872881025024"
def inputClause6698 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inputList6698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6698 (by decide) v hb
mask_input "6698|310089694096584867454124032|38695070960633872883122176"
def inputClause6699 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inputList6699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6699 (by decide) v hb
mask_input "6699|310089620309608572618014720|38695144747610167719231488"
def inputClause6700 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inputList6700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6700 (by decide) v hb
mask_input "6700|310089620309608572615917568|38695144747610167721328640"
def inputClause6703 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,true),(88,false)]
theorem inputList6703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6703 (by decide) v hb
mask_input "6703|310089472735655982941601792|38695292321562757395644416"
def inputClause6704 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,true),(88,false)]
theorem inputList6704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6704 (by decide) v hb
mask_input "6704|310089472735655982939504640|38695292321562757397741568"
def inputClause6705 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inputList6705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6705 (by decide) v hb
mask_input "6705|309494675919743292159295488|39290089137475448177950720"
def inputClause6706 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inputList6706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6706 (by decide) v hb
mask_input "6706|309494675919743292157198336|39290089137475448180047872"
def inputClause6707 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inputList6707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6707 (by decide) v hb
mask_input "6707|309494602132766997321089024|39290162924451743016157184"
def inputClause6708 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inputList6708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6708 (by decide) v hb
mask_input "6708|309494602132766997318991872|39290162924451743018254336"
def inputClause6712 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,true),(88,false)]
theorem inputList6712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6712 (by decide) v hb
mask_input "6712|309494454558814407642578944|39290310498404332694667264"
def inputClause6713 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inputList6713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6713 (by decide) v hb
mask_input "6713|309485231186777552868868096|39299533870441187468378112"
def inputClause6714 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inputList6714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6714 (by decide) v hb
mask_input "6714|309485231186777552866770944|39299533870441187470475264"
def inputClause6715 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inputList6715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6715 (by decide) v hb
mask_input "6715|309485157399801258030661632|39299607657417482306584576"
def inputClause6716 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,true),(88,false)]
theorem inputList6716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6716 (by decide) v hb
mask_input "6716|309485157399801258028564480|39299607657417482308681728"
def inputClause6720 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,true),(88,false)]
theorem inputList6720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6720 (by decide) v hb
mask_input "6720|309485009825848668352151552|39299755231370071985094656"
def inputClause6721 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6721 (by decide) v hb
mask_input "6721|39299755235873671612465152|309485009821345068724781056"
def inputClause6722 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6722 (by decide) v hb
mask_input "6722|39299755235873671610368000|309485009821345068726878208"
def inputClause6723 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6723 (by decide) v hb
mask_input "6723|39299681448897376774258688|309485083608321363562987520"
def inputClause6724 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6724 (by decide) v hb
mask_input "6724|39299681448897376772161536|309485083608321363565084672"
def inputClause6725 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6725 (by decide) v hb
mask_input "6725|39299607661921081936052224|309485157395297658401193984"
def inputClause6727 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6727 (by decide) v hb
mask_input "6727|39299533874944787097845760|309485231182273953239400448"
def inputClause6728 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6728 (by decide) v hb
mask_input "6728|39299533874944787095748608|309485231182273953241497600"
def inputClause6729 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6729 (by decide) v hb
mask_input "6729|39290310502907932322037760|309494454554310808015208448"
def inputClause6730 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6730 (by decide) v hb
mask_input "6730|39290310502907932319940608|309494454554310808017305600"
def inputClause6731 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6731 (by decide) v hb
mask_input "6731|39290236715931637483831296|309494528341287102853414912"
def inputClause6732 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6732 (by decide) v hb
mask_input "6732|39290236715931637481734144|309494528341287102855512064"
def inputClause6733 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6733 (by decide) v hb
mask_input "6733|39290162928955342645624832|309494602128263397691621376"
def inputClause6735 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6735 (by decide) v hb
mask_input "6735|39290089141979047807418368|309494675915239692529827840"
def inputClause6736 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6736 (by decide) v hb
mask_input "6736|39290089141979047805321216|309494675915239692531924992"
end Percolation.MaskChain
