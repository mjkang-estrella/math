import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause416 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,true),(29,false)]
theorem inputList416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause416 (by decide) v hb
mask_input "416|295147905179889696768|1118480"
def inputClause432 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,true),(20,false),(29,true)]
theorem inputList432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause432 (by decide) v hb
mask_input "432|295147905179353874432|536940816"
def inputClause440 : CNF.NClause := [(68,false),(4,true),(8,true),(12,true),(16,false),(20,true),(29,true)]
theorem inputList440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause440 (by decide) v hb
mask_input "440|295147905179352891392|537923856"
def inputClause444 : CNF.NClause := [(68,false),(4,true),(8,true),(12,false),(16,true),(20,true),(29,true)]
theorem inputList444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause444 (by decide) v hb
mask_input "444|295147905179352829952|537985296"
def inputClause446 : CNF.NClause := [(68,false),(4,true),(8,false),(12,true),(16,true),(20,true),(29,true)]
theorem inputList446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause446 (by decide) v hb
mask_input "446|295147905179352826112|537989136"
def inputClause480 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,true),(27,false)]
theorem inputList480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause480 (by decide) v hb
mask_input "480|590295810358839869440|1313284"
def inputClause496 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,true),(20,false),(27,true)]
theorem inputList496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause496 (by decide) v hb
mask_input "496|590295810358706700288|134482436"
def inputClause504 : CNF.NClause := [(69,false),(2,true),(9,true),(11,true),(18,false),(20,true),(27,true)]
theorem inputList504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause504 (by decide) v hb
mask_input "504|590295810358705913856|135268868"
def inputClause508 : CNF.NClause := [(69,false),(2,true),(9,true),(11,false),(18,true),(20,true),(27,true)]
theorem inputList508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause508 (by decide) v hb
mask_input "508|590295810358705653760|135528964"
def inputClause511 : CNF.NClause := [(69,false),(2,false),(9,true),(11,true),(18,true),(20,true),(27,true)]
theorem inputList511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 7) 7) (activationA_mem 7) inputClause511 (by decide) v hb
mask_input "511|590295810358705651716|135531008"
def inputClause544 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,true),(20,true),(28,false)]
theorem inputList544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause544 (by decide) v hb
mask_input "544|1180591620717679738880|1196104"
def inputClause560 : CNF.NClause := [(70,false),(3,true),(6,true),(14,true),(17,true),(20,false),(28,true)]
theorem inputList560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause560 (by decide) v hb
mask_input "560|1180591620717412352000|268582984"
def inputClause572 : CNF.NClause := [(70,false),(3,true),(6,true),(14,false),(17,true),(20,true),(28,true)]
theorem inputList572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause572 (by decide) v hb
mask_input "572|1180591620717411319808|269615176"
def inputClause574 : CNF.NClause := [(70,false),(3,true),(6,false),(14,true),(17,true),(20,true),(28,true)]
theorem inputList574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause574 (by decide) v hb
mask_input "574|1180591620717411303488|269631496"
def inputClause624 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,false),(26,true)]
theorem inputList624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause624 (by decide) v hb
mask_input "624|2361183241434823655424|67641474"
def inputClause632 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,false),(20,true),(26,true)]
theorem inputList632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause632 (by decide) v hb
mask_input "632|2361183241434823131136|68165762"
def inputClause636 : CNF.NClause := [(71,false),(1,true),(7,true),(13,false),(19,true),(20,true),(26,true)]
theorem inputList636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause636 (by decide) v hb
mask_input "636|2361183241434822615040|68681858"
def inputClause638 : CNF.NClause := [(71,false),(1,true),(7,false),(13,true),(19,true),(20,true),(26,true)]
theorem inputList638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause638 (by decide) v hb
mask_input "638|2361183241434822606976|68689922"
def inputClause639 : CNF.NClause := [(71,false),(1,false),(7,true),(13,true),(19,true),(20,true),(26,true)]
theorem inputList639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause639 (by decide) v hb
mask_input "639|2361183241434822606850|68690048"
def inputClause736 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,true),(28,false)]
theorem inputList736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause736 (by decide) v hb
mask_input "736|9444732965739558862848|2360464"
def inputClause752 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,false),(28,true)]
theorem inputList752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause752 (by decide) v hb
mask_input "752|9444732965739292524544|268698768"
def inputClause760 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,false),(21,true),(28,true)]
theorem inputList760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause760 (by decide) v hb
mask_input "760|9444732965739290689536|270533776"
def inputClause764 : CNF.NClause := [(73,false),(4,true),(7,true),(10,false),(18,true),(21,true),(28,true)]
theorem inputList764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause764 (by decide) v hb
mask_input "764|9444732965739290428416|270794896"
def inputClause767 : CNF.NClause := [(73,false),(4,false),(7,true),(10,true),(18,true),(21,true),(28,true)]
theorem inputList767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause767 (by decide) v hb
mask_input "767|9444732965739290427408|270795904"
def inputClause800 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,true),(29,false)]
theorem inputList800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause800 (by decide) v hb
mask_input "800|18889465931479117725696|8913988"
def inputClause816 : CNF.NClause := [(74,false),(2,true),(6,true),(10,true),(19,true),(23,false),(29,true)]
theorem inputList816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause816 (by decide) v hb
mask_input "816|18889465931478589243392|537396292"
def inputClause828 : CNF.NClause := [(74,false),(2,true),(6,true),(10,false),(19,true),(23,true),(29,true)]
theorem inputList828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause828 (by decide) v hb
mask_input "828|18889465931478580855808|545783876"
def inputClause830 : CNF.NClause := [(74,false),(2,true),(6,false),(10,true),(19,true),(23,true),(29,true)]
theorem inputList830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause830 (by decide) v hb
mask_input "830|18889465931478580854848|545784836"
def inputClause831 : CNF.NClause := [(74,false),(2,false),(6,true),(10,true),(19,true),(23,true),(29,true)]
theorem inputList831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause831 (by decide) v hb
mask_input "831|18889465931478580854788|545784896"
def inputClause864 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,true),(22,true),(26,false)]
theorem inputList864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause864 (by decide) v hb
mask_input "864|37778931862957228818432|4261384"
def inputClause880 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,true),(22,false),(26,true)]
theorem inputList880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause880 (by decide) v hb
mask_input "880|37778931862957165903872|67175944"
def inputClause888 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,false),(22,true),(26,true)]
theorem inputList888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause888 (by decide) v hb
mask_input "888|37778931862957161775104|71304712"
def inputClause892 : CNF.NClause := [(75,false),(3,true),(9,true),(10,false),(16,true),(22,true),(26,true)]
theorem inputList892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause892 (by decide) v hb
mask_input "892|37778931862957161710592|71369224"
def inputClause895 : CNF.NClause := [(75,false),(3,false),(9,true),(10,true),(16,true),(22,true),(26,true)]
theorem inputList895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause895 (by decide) v hb
mask_input "895|37778931862957161709576|71370240"
def inputClause944 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,false),(27,true)]
theorem inputList944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause944 (by decide) v hb
mask_input "944|75557863725914340196352|134350082"
def inputClause952 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,false),(24,true),(27,true)]
theorem inputList952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause952 (by decide) v hb
mask_input "952|75557863725914323550208|150996226"
def inputClause956 : CNF.NClause := [(76,false),(1,true),(8,true),(10,false),(17,true),(24,true),(27,true)]
theorem inputList956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause956 (by decide) v hb
mask_input "956|75557863725914323420160|151126274"
def inputClause958 : CNF.NClause := [(76,false),(1,true),(8,false),(10,true),(17,true),(24,true),(27,true)]
theorem inputList958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause958 (by decide) v hb
mask_input "958|75557863725914323419392|151127042"
def inputClause959 : CNF.NClause := [(76,false),(1,false),(8,true),(10,true),(17,true),(24,true),(27,true)]
theorem inputList959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause959 (by decide) v hb
mask_input "959|75557863725914323419138|151127296"
def inputClause1072 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,false),(27,true)]
theorem inputList1072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1072 (by decide) v hb
mask_input "1072|302231454903657297870848|134258768"
end Percolation.MaskChain
