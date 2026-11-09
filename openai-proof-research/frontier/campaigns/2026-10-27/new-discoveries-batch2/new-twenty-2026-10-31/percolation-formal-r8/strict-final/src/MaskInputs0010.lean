import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause629 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,true),(26,true)]
theorem inputList629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause629 (by decide) v hb
mask_input "629|524418|2361183241434890772480"
def inputClause630 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,true),(26,true)]
theorem inputList630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause630 (by decide) v hb
mask_input "630|524416|2361183241434890772482"
def inputClause631 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,true),(26,true)]
theorem inputList631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause631 (by decide) v hb
mask_input "631|524290|2361183241434890772608"
def inputClause633 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,true),(26,true)]
theorem inputList633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause633 (by decide) v hb
mask_input "633|8322|2361183241434891288576"
def inputClause634 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,true),(26,true)]
theorem inputList634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause634 (by decide) v hb
mask_input "634|8320|2361183241434891288578"
def inputClause635 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,true),(26,true)]
theorem inputList635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause635 (by decide) v hb
mask_input "635|8194|2361183241434891288704"
def inputClause637 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,true),(26,true)]
theorem inputList637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause637 (by decide) v hb
mask_input "637|130|2361183241434891296768"
def inputClause640 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,true),(26,true)]
theorem inputList640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause640 (by decide) v hb
mask_input "640|2361183241434822606848|68690050"
def inputClause673 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,false),(30,true)]
theorem inputList673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause673 (by decide) v hb
mask_input "673|31744|4722366482870718955520"
def inputClause674 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,false),(30,true)]
theorem inputList674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause674 (by decide) v hb
mask_input "674|30720|4722366482870718956544"
def inputClause675 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,false),(14,false),(30,true)]
theorem inputList675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause675 (by decide) v hb
mask_input "675|29696|4722366482870718957568"
def inputClause676 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,false),(14,false),(30,true)]
theorem inputList676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause676 (by decide) v hb
mask_input "676|28672|4722366482870718958592"
def inputClause677 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,false),(30,true)]
theorem inputList677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause677 (by decide) v hb
mask_input "677|27648|4722366482870718959616"
def inputClause678 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,false),(30,true)]
theorem inputList678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause678 (by decide) v hb
mask_input "678|26624|4722366482870718960640"
def inputClause679 : CNF.NClause := [(72,true),(10,false),(11,true),(12,true),(13,false),(14,false),(30,true)]
theorem inputList679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause679 (by decide) v hb
mask_input "679|25600|4722366482870718961664"
def inputClause680 : CNF.NClause := [(72,true),(10,true),(11,true),(12,true),(13,false),(14,false),(30,true)]
theorem inputList680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause680 (by decide) v hb
mask_input "680|24576|4722366482870718962688"
def inputClause681 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,true),(14,false),(30,true)]
theorem inputList681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause681 (by decide) v hb
mask_input "681|23552|4722366482870718963712"
def inputClause682 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,false),(30,true)]
theorem inputList682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause682 (by decide) v hb
mask_input "682|22528|4722366482870718964736"
def inputClause683 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,true),(14,false),(30,true)]
theorem inputList683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause683 (by decide) v hb
mask_input "683|21504|4722366482870718965760"
def inputClause684 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,true),(14,false),(30,true)]
theorem inputList684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause684 (by decide) v hb
mask_input "684|20480|4722366482870718966784"
def inputClause685 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,false),(30,true)]
theorem inputList685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause685 (by decide) v hb
mask_input "685|19456|4722366482870718967808"
def inputClause686 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,true),(14,false),(30,true)]
theorem inputList686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause686 (by decide) v hb
mask_input "686|18432|4722366482870718968832"
def inputClause687 : CNF.NClause := [(72,true),(10,false),(11,true),(12,true),(13,true),(14,false),(30,true)]
theorem inputList687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause687 (by decide) v hb
mask_input "687|17408|4722366482870718969856"
def inputClause688 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,true),(14,false),(30,true)]
theorem inputList688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause688 (by decide) v hb
mask_input "688|4722366482869645230080|1073757184"
def inputClause689 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,true),(30,true)]
theorem inputList689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause689 (by decide) v hb
mask_input "689|15360|4722366482870718971904"
def inputClause690 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,true),(30,true)]
theorem inputList690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause690 (by decide) v hb
mask_input "690|14336|4722366482870718972928"
def inputClause691 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,false),(14,true),(30,true)]
theorem inputList691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause691 (by decide) v hb
mask_input "691|13312|4722366482870718973952"
def inputClause692 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,false),(14,true),(30,true)]
theorem inputList692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause692 (by decide) v hb
mask_input "692|12288|4722366482870718974976"
def inputClause693 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,true),(30,true)]
theorem inputList693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause693 (by decide) v hb
mask_input "693|11264|4722366482870718976000"
def inputClause694 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,true),(30,true)]
theorem inputList694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause694 (by decide) v hb
mask_input "694|10240|4722366482870718977024"
def inputClause695 : CNF.NClause := [(72,true),(10,false),(11,true),(12,true),(13,false),(14,true),(30,true)]
theorem inputList695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause695 (by decide) v hb
mask_input "695|9216|4722366482870718978048"
def inputClause696 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,false),(14,true),(30,true)]
theorem inputList696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause696 (by decide) v hb
mask_input "696|4722366482869645221888|1073765376"
def inputClause697 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,true),(14,true),(30,true)]
theorem inputList697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause697 (by decide) v hb
mask_input "697|7168|4722366482870718980096"
def inputClause698 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,true),(30,true)]
theorem inputList698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause698 (by decide) v hb
mask_input "698|6144|4722366482870718981120"
def inputClause699 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,true),(14,true),(30,true)]
theorem inputList699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause699 (by decide) v hb
mask_input "699|5120|4722366482870718982144"
def inputClause700 : CNF.NClause := [(72,false),(10,true),(11,true),(12,false),(13,true),(14,true),(30,true)]
theorem inputList700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause700 (by decide) v hb
mask_input "700|4722366482869645217792|1073769472"
def inputClause701 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,true),(30,true)]
theorem inputList701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause701 (by decide) v hb
mask_input "701|3072|4722366482870718984192"
def inputClause702 : CNF.NClause := [(72,false),(10,true),(11,false),(12,true),(13,true),(14,true),(30,true)]
theorem inputList702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause702 (by decide) v hb
mask_input "702|4722366482869645215744|1073771520"
def inputClause703 : CNF.NClause := [(72,false),(10,false),(11,true),(12,true),(13,true),(14,true),(30,true)]
theorem inputList703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause703 (by decide) v hb
mask_input "703|4722366482869645214720|1073772544"
def inputClause704 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,true),(14,true),(30,true)]
theorem inputList704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) inputClause704 (by decide) v hb
mask_input "704|4722366482869645213696|1073773568"
end Percolation.MaskChain
