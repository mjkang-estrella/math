import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause705 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,false),(28,false)]
theorem inputList705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause705 (by decide) v hb
mask_input "705|270795920|9444732965739290427392"
def inputClause706 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,false),(28,false)]
theorem inputList706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause706 (by decide) v hb
mask_input "706|270795904|9444732965739290427408"
def inputClause707 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,false),(28,false)]
theorem inputList707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause707 (by decide) v hb
mask_input "707|270795792|9444732965739290427520"
def inputClause708 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,false),(28,false)]
theorem inputList708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause708 (by decide) v hb
mask_input "708|270795776|9444732965739290427536"
def inputClause709 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,false),(28,false)]
theorem inputList709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause709 (by decide) v hb
mask_input "709|270794896|9444732965739290428416"
def inputClause710 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,false),(28,false)]
theorem inputList710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause710 (by decide) v hb
mask_input "710|270794880|9444732965739290428432"
def inputClause711 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,false),(28,false)]
theorem inputList711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause711 (by decide) v hb
mask_input "711|270794768|9444732965739290428544"
def inputClause712 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,false),(28,false)]
theorem inputList712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause712 (by decide) v hb
mask_input "712|270794752|9444732965739290428560"
def inputClause713 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,false),(28,false)]
theorem inputList713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause713 (by decide) v hb
mask_input "713|270533776|9444732965739290689536"
def inputClause714 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,false),(28,false)]
theorem inputList714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause714 (by decide) v hb
mask_input "714|270533760|9444732965739290689552"
def inputClause715 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,false),(28,false)]
theorem inputList715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause715 (by decide) v hb
mask_input "715|270533648|9444732965739290689664"
def inputClause716 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,false),(28,false)]
theorem inputList716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause716 (by decide) v hb
mask_input "716|270533632|9444732965739290689680"
def inputClause717 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,false),(28,false)]
theorem inputList717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause717 (by decide) v hb
mask_input "717|270532752|9444732965739290690560"
def inputClause718 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,true),(21,false),(28,false)]
theorem inputList718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause718 (by decide) v hb
mask_input "718|270532736|9444732965739290690576"
def inputClause719 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,false),(28,false)]
theorem inputList719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause719 (by decide) v hb
mask_input "719|270532624|9444732965739290690688"
def inputClause720 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,true),(21,false),(28,false)]
theorem inputList720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause720 (by decide) v hb
mask_input "720|270532608|9444732965739290690704"
def inputClause721 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,true),(28,false)]
theorem inputList721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause721 (by decide) v hb
mask_input "721|268698768|9444732965739292524544"
def inputClause722 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,true),(28,false)]
theorem inputList722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause722 (by decide) v hb
mask_input "722|268698752|9444732965739292524560"
def inputClause723 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,true),(28,false)]
theorem inputList723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause723 (by decide) v hb
mask_input "723|268698640|9444732965739292524672"
def inputClause724 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,true),(28,false)]
theorem inputList724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause724 (by decide) v hb
mask_input "724|268698624|9444732965739292524688"
def inputClause725 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,true),(28,false)]
theorem inputList725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause725 (by decide) v hb
mask_input "725|268697744|9444732965739292525568"
def inputClause726 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,true),(28,false)]
theorem inputList726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause726 (by decide) v hb
mask_input "726|268697728|9444732965739292525584"
def inputClause727 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,true),(28,false)]
theorem inputList727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause727 (by decide) v hb
mask_input "727|268697616|9444732965739292525696"
def inputClause728 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,true),(28,false)]
theorem inputList728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause728 (by decide) v hb
mask_input "728|268697600|9444732965739292525712"
def inputClause729 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,true),(28,false)]
theorem inputList729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause729 (by decide) v hb
mask_input "729|268436624|9444732965739292786688"
def inputClause730 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,true),(28,false)]
theorem inputList730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause730 (by decide) v hb
mask_input "730|268436608|9444732965739292786704"
def inputClause731 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,true),(28,false)]
theorem inputList731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause731 (by decide) v hb
mask_input "731|268436496|9444732965739292786816"
def inputClause732 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,true),(28,false)]
theorem inputList732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause732 (by decide) v hb
mask_input "732|268436480|9444732965739292786832"
def inputClause733 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,true),(28,false)]
theorem inputList733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause733 (by decide) v hb
mask_input "733|268435600|9444732965739292787712"
def inputClause734 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,true),(21,true),(28,false)]
theorem inputList734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause734 (by decide) v hb
mask_input "734|268435584|9444732965739292787728"
def inputClause735 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,true),(28,false)]
theorem inputList735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause735 (by decide) v hb
mask_input "735|268435472|9444732965739292787840"
def inputClause737 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,false),(28,true)]
theorem inputList737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause737 (by decide) v hb
mask_input "737|2360464|9444732965739558862848"
def inputClause738 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,false),(28,true)]
theorem inputList738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause738 (by decide) v hb
mask_input "738|2360448|9444732965739558862864"
def inputClause739 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,false),(28,true)]
theorem inputList739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause739 (by decide) v hb
mask_input "739|2360336|9444732965739558862976"
def inputClause740 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,false),(28,true)]
theorem inputList740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause740 (by decide) v hb
mask_input "740|2360320|9444732965739558862992"
def inputClause741 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,false),(28,true)]
theorem inputList741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause741 (by decide) v hb
mask_input "741|2359440|9444732965739558863872"
def inputClause742 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,false),(28,true)]
theorem inputList742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause742 (by decide) v hb
mask_input "742|2359424|9444732965739558863888"
def inputClause743 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,false),(28,true)]
theorem inputList743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause743 (by decide) v hb
mask_input "743|2359312|9444732965739558864000"
def inputClause744 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,false),(28,true)]
theorem inputList744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause744 (by decide) v hb
mask_input "744|2359296|9444732965739558864016"
def inputClause745 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,false),(28,true)]
theorem inputList745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause745 (by decide) v hb
mask_input "745|2098320|9444732965739559124992"
end Percolation.MaskChain
