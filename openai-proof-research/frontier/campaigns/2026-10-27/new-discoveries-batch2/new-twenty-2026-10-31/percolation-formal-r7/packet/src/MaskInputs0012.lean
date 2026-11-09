import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause746 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,false),(28,true)]
theorem inputList746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause746 (by decide) v hb
mask_input "746|2098304|9444732965739559125008"
def inputClause747 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,false),(28,true)]
theorem inputList747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause747 (by decide) v hb
mask_input "747|2098192|9444732965739559125120"
def inputClause748 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,false),(28,true)]
theorem inputList748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause748 (by decide) v hb
mask_input "748|2098176|9444732965739559125136"
def inputClause749 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,false),(28,true)]
theorem inputList749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause749 (by decide) v hb
mask_input "749|2097296|9444732965739559126016"
def inputClause750 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,true),(21,false),(28,true)]
theorem inputList750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause750 (by decide) v hb
mask_input "750|2097280|9444732965739559126032"
def inputClause751 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,false),(28,true)]
theorem inputList751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause751 (by decide) v hb
mask_input "751|2097168|9444732965739559126144"
def inputClause753 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,true),(28,true)]
theorem inputList753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause753 (by decide) v hb
mask_input "753|263312|9444732965739560960000"
def inputClause754 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,true),(28,true)]
theorem inputList754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause754 (by decide) v hb
mask_input "754|263296|9444732965739560960016"
def inputClause755 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,true),(28,true)]
theorem inputList755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause755 (by decide) v hb
mask_input "755|263184|9444732965739560960128"
def inputClause756 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,true),(28,true)]
theorem inputList756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause756 (by decide) v hb
mask_input "756|263168|9444732965739560960144"
def inputClause757 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,true),(28,true)]
theorem inputList757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause757 (by decide) v hb
mask_input "757|262288|9444732965739560961024"
def inputClause758 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,true),(28,true)]
theorem inputList758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause758 (by decide) v hb
mask_input "758|262272|9444732965739560961040"
def inputClause759 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,true),(28,true)]
theorem inputList759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause759 (by decide) v hb
mask_input "759|262160|9444732965739560961152"
def inputClause761 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,true),(28,true)]
theorem inputList761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause761 (by decide) v hb
mask_input "761|1168|9444732965739561222144"
def inputClause762 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,true),(28,true)]
theorem inputList762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause762 (by decide) v hb
mask_input "762|1152|9444732965739561222160"
def inputClause763 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,true),(28,true)]
theorem inputList763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause763 (by decide) v hb
mask_input "763|1040|9444732965739561222272"
def inputClause765 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,true),(21,true),(28,true)]
theorem inputList765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause765 (by decide) v hb
mask_input "765|144|9444732965739561223168"
def inputClause766 : CNF.NClause := [(73,false),(4,true),(7,false),(10,true),(18,true),(21,true),(28,true)]
theorem inputList766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause766 (by decide) v hb
mask_input "766|9444732965739290427520|270795792"
def inputClause768 : CNF.NClause := [(73,false),(4,true),(7,true),(10,true),(18,true),(21,true),(28,true)]
theorem inputList768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) inputClause768 (by decide) v hb
mask_input "768|9444732965739290427392|270795920"
def inputClause769 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,false),(29,false)]
theorem inputList769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause769 (by decide) v hb
mask_input "769|545784900|18889465931478580854784"
def inputClause770 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,false),(29,false)]
theorem inputList770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause770 (by decide) v hb
mask_input "770|545784896|18889465931478580854788"
def inputClause771 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,false),(29,false)]
theorem inputList771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause771 (by decide) v hb
mask_input "771|545784836|18889465931478580854848"
def inputClause772 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,false),(29,false)]
theorem inputList772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause772 (by decide) v hb
mask_input "772|545784832|18889465931478580854852"
def inputClause773 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,false),(29,false)]
theorem inputList773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause773 (by decide) v hb
mask_input "773|545783876|18889465931478580855808"
def inputClause774 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,false),(23,false),(29,false)]
theorem inputList774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause774 (by decide) v hb
mask_input "774|545783872|18889465931478580855812"
def inputClause775 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,false),(23,false),(29,false)]
theorem inputList775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause775 (by decide) v hb
mask_input "775|545783812|18889465931478580855872"
def inputClause776 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,false),(23,false),(29,false)]
theorem inputList776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause776 (by decide) v hb
mask_input "776|545783808|18889465931478580855876"
def inputClause777 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,true),(23,false),(29,false)]
theorem inputList777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause777 (by decide) v hb
mask_input "777|545260612|18889465931478581379072"
def inputClause778 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,true),(23,false),(29,false)]
theorem inputList778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause778 (by decide) v hb
mask_input "778|545260608|18889465931478581379076"
def inputClause779 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,true),(23,false),(29,false)]
theorem inputList779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause779 (by decide) v hb
mask_input "779|545260548|18889465931478581379136"
def inputClause780 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,true),(23,false),(29,false)]
theorem inputList780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause780 (by decide) v hb
mask_input "780|545260544|18889465931478581379140"
def inputClause781 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,false),(29,false)]
theorem inputList781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause781 (by decide) v hb
mask_input "781|545259588|18889465931478581380096"
def inputClause782 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(23,false),(29,false)]
theorem inputList782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause782 (by decide) v hb
mask_input "782|545259584|18889465931478581380100"
def inputClause783 : CNF.NClause := [(74,true),(2,false),(6,true),(10,true),(19,true),(23,false),(29,false)]
theorem inputList783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause783 (by decide) v hb
mask_input "783|545259524|18889465931478581380160"
def inputClause784 : CNF.NClause := [(74,true),(2,true),(6,true),(10,true),(19,true),(23,false),(29,false)]
theorem inputList784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause784 (by decide) v hb
mask_input "784|545259520|18889465931478581380164"
def inputClause785 : CNF.NClause := [(74,true),(2,false),(6,false),(10,false),(19,false),(23,true),(29,false)]
theorem inputList785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause785 (by decide) v hb
mask_input "785|537396292|18889465931478589243392"
def inputClause786 : CNF.NClause := [(74,true),(2,true),(6,false),(10,false),(19,false),(23,true),(29,false)]
theorem inputList786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause786 (by decide) v hb
mask_input "786|537396288|18889465931478589243396"
def inputClause787 : CNF.NClause := [(74,true),(2,false),(6,true),(10,false),(19,false),(23,true),(29,false)]
theorem inputList787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause787 (by decide) v hb
mask_input "787|537396228|18889465931478589243456"
def inputClause788 : CNF.NClause := [(74,true),(2,true),(6,true),(10,false),(19,false),(23,true),(29,false)]
theorem inputList788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause788 (by decide) v hb
mask_input "788|537396224|18889465931478589243460"
def inputClause789 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,false),(23,true),(29,false)]
theorem inputList789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 12) 12) (activationA_mem 12) inputClause789 (by decide) v hb
mask_input "789|537395268|18889465931478589244416"
end Percolation.MaskChain
