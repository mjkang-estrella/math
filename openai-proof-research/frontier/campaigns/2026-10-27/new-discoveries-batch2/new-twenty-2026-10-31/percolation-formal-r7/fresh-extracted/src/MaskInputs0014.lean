import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause835 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,false),(26,false)]
theorem inputList835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause835 (by decide) v hb
mask_input "835|71369736|37778931862957161710080"
def inputClause836 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,false),(26,false)]
theorem inputList836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause836 (by decide) v hb
mask_input "836|71369728|37778931862957161710088"
def inputClause837 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,false),(26,false)]
theorem inputList837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause837 (by decide) v hb
mask_input "837|71369224|37778931862957161710592"
def inputClause838 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,false),(26,false)]
theorem inputList838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause838 (by decide) v hb
mask_input "838|71369216|37778931862957161710600"
def inputClause839 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,false),(26,false)]
theorem inputList839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause839 (by decide) v hb
mask_input "839|71368712|37778931862957161711104"
def inputClause840 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,false),(26,false)]
theorem inputList840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause840 (by decide) v hb
mask_input "840|71368704|37778931862957161711112"
def inputClause841 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,false),(26,false)]
theorem inputList841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause841 (by decide) v hb
mask_input "841|71304712|37778931862957161775104"
def inputClause842 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,false),(26,false)]
theorem inputList842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause842 (by decide) v hb
mask_input "842|71304704|37778931862957161775112"
def inputClause843 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,false),(26,false)]
theorem inputList843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause843 (by decide) v hb
mask_input "843|71304200|37778931862957161775616"
def inputClause844 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,false),(26,false)]
theorem inputList844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause844 (by decide) v hb
mask_input "844|71304192|37778931862957161775624"
def inputClause845 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,false),(26,false)]
theorem inputList845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause845 (by decide) v hb
mask_input "845|71303688|37778931862957161776128"
def inputClause846 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,false),(26,false)]
theorem inputList846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause846 (by decide) v hb
mask_input "846|71303680|37778931862957161776136"
def inputClause847 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,false),(26,false)]
theorem inputList847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause847 (by decide) v hb
mask_input "847|71303176|37778931862957161776640"
def inputClause848 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,true),(22,false),(26,false)]
theorem inputList848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause848 (by decide) v hb
mask_input "848|71303168|37778931862957161776648"
def inputClause849 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,true),(26,false)]
theorem inputList849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause849 (by decide) v hb
mask_input "849|67175944|37778931862957165903872"
def inputClause850 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,true),(26,false)]
theorem inputList850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause850 (by decide) v hb
mask_input "850|67175936|37778931862957165903880"
def inputClause851 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,true),(26,false)]
theorem inputList851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause851 (by decide) v hb
mask_input "851|67175432|37778931862957165904384"
def inputClause852 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,true),(26,false)]
theorem inputList852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause852 (by decide) v hb
mask_input "852|67175424|37778931862957165904392"
def inputClause853 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,true),(26,false)]
theorem inputList853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause853 (by decide) v hb
mask_input "853|67174920|37778931862957165904896"
def inputClause854 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,true),(26,false)]
theorem inputList854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause854 (by decide) v hb
mask_input "854|67174912|37778931862957165904904"
def inputClause855 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,true),(26,false)]
theorem inputList855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause855 (by decide) v hb
mask_input "855|67174408|37778931862957165905408"
def inputClause856 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,true),(26,false)]
theorem inputList856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause856 (by decide) v hb
mask_input "856|67174400|37778931862957165905416"
def inputClause857 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,true),(26,false)]
theorem inputList857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause857 (by decide) v hb
mask_input "857|67110408|37778931862957165969408"
def inputClause858 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,true),(26,false)]
theorem inputList858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause858 (by decide) v hb
mask_input "858|67110400|37778931862957165969416"
def inputClause859 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,true),(26,false)]
theorem inputList859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause859 (by decide) v hb
mask_input "859|67109896|37778931862957165969920"
def inputClause860 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,true),(26,false)]
theorem inputList860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause860 (by decide) v hb
mask_input "860|67109888|37778931862957165969928"
def inputClause861 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,true),(26,false)]
theorem inputList861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause861 (by decide) v hb
mask_input "861|67109384|37778931862957165970432"
def inputClause862 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,true),(26,false)]
theorem inputList862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause862 (by decide) v hb
mask_input "862|67109376|37778931862957165970440"
def inputClause863 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,true),(26,false)]
theorem inputList863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause863 (by decide) v hb
mask_input "863|67108872|37778931862957165970944"
def inputClause865 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,false),(26,true)]
theorem inputList865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause865 (by decide) v hb
mask_input "865|4261384|37778931862957228818432"
def inputClause866 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,false),(26,true)]
theorem inputList866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause866 (by decide) v hb
mask_input "866|4261376|37778931862957228818440"
def inputClause867 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,false),(26,true)]
theorem inputList867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause867 (by decide) v hb
mask_input "867|4260872|37778931862957228818944"
def inputClause868 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,false),(26,true)]
theorem inputList868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause868 (by decide) v hb
mask_input "868|4260864|37778931862957228818952"
def inputClause869 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,false),(26,true)]
theorem inputList869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause869 (by decide) v hb
mask_input "869|4260360|37778931862957228819456"
def inputClause870 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,false),(26,true)]
theorem inputList870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause870 (by decide) v hb
mask_input "870|4260352|37778931862957228819464"
def inputClause871 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,false),(26,true)]
theorem inputList871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause871 (by decide) v hb
mask_input "871|4259848|37778931862957228819968"
def inputClause872 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,false),(26,true)]
theorem inputList872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause872 (by decide) v hb
mask_input "872|4259840|37778931862957228819976"
def inputClause873 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,false),(26,true)]
theorem inputList873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause873 (by decide) v hb
mask_input "873|4195848|37778931862957228883968"
def inputClause874 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,false),(26,true)]
theorem inputList874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause874 (by decide) v hb
mask_input "874|4195840|37778931862957228883976"
def inputClause875 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,false),(26,true)]
theorem inputList875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause875 (by decide) v hb
mask_input "875|4195336|37778931862957228884480"
end Percolation.MaskChain
