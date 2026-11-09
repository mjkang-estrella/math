import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4606 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4606 (by decide) v hb
mask_input "4606|9223372071214514176|164725882803364143696969744"
def inputClause4607 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4607 (by decide) v hb
mask_input "4607|34359738384|164725892026736180551745536"
def inputClause4608 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4608 (by decide) v hb
mask_input "4608|34359738368|164725892026736180551745552"
def inputClause4609 : CNF.NClause := [(36,true),(5,false),(82,false),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inputList4609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4609 (by decide) v hb
mask_input "4609|5101666958773735117260062752|68719476736"
def inputClause4737 : CNF.NClause := [(37,true),(6,false),(66,false),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4737 (by decide) v hb
mask_input "4737|2481038157148651214621114432|137438953472"
def inputClause4801 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4801 (by decide) v hb
mask_input "4801|5158078577890802261819456|2475880078570760549798248448"
def inputClause4865 : CNF.NClause := [(38,true),(7,false),(64,false),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4865 (by decide) v hb
mask_input "4865|625026473103714531145678976|274877906944"
def inputClause4866 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4866 (by decide) v hb
mask_input "4866|625026473103714806023585792|128"
def inputClause4867 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4867 (by decide) v hb
mask_input "4867|625026454656970732314034304|18446744073709551616"
def inputClause4868 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4868 (by decide) v hb
mask_input "4868|625026454656970732314034176|18446744073709551744"
def inputClause4869 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4869 (by decide) v hb
mask_input "4869|625024111920473371200979072|2361183241434822606848"
def inputClause4870 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4870 (by decide) v hb
mask_input "4870|625024111920473371200978944|2361183241434822606976"
def inputClause4871 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4871 (by decide) v hb
mask_input "4871|625024093473729297491427456|2379629985508532158464"
def inputClause4872 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inputList4872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4872 (by decide) v hb
mask_input "4872|625024093473729297491427328|2379629985508532158592"
def inputClause4873 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4873 (by decide) v hb
mask_input "4873|625017028370749066733158528|9444732965739290427392"
def inputClause4874 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4874 (by decide) v hb
mask_input "4874|625017028370749066733158400|9444732965739290427520"
def inputClause4875 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4875 (by decide) v hb
mask_input "4875|625017009924004993023606912|9463179709812999979008"
def inputClause4876 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4876 (by decide) v hb
mask_input "4876|625017009924004993023606784|9463179709812999979136"
def inputClause4877 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4877 (by decide) v hb
mask_input "4877|625014667187507631910551680|11805916207174113034240"
def inputClause4878 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4878 (by decide) v hb
mask_input "4878|625014667187507631910551552|11805916207174113034368"
def inputClause4879 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4879 (by decide) v hb
mask_input "4879|625014648740763558201000064|11824362951247822585856"
def inputClause4880 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inputList4880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4880 (by decide) v hb
mask_input "4880|625014648740763558200999936|11824362951247822585984"
def inputClause4881 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4881 (by decide) v hb
mask_input "4881|623817547284100176848879744|1208925819614629174706176"
def inputClause4882 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4882 (by decide) v hb
mask_input "4882|623817547284100176848879616|1208925819614629174706304"
def inputClause4883 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4883 (by decide) v hb
mask_input "4883|623817528837356103139328128|1208944266358702884257792"
def inputClause4884 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4884 (by decide) v hb
mask_input "4884|623817528837356103139328000|1208944266358702884257920"
def inputClause4885 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4885 (by decide) v hb
mask_input "4885|623815186100858742026272896|1211287002856063997313024"
def inputClause4886 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4886 (by decide) v hb
mask_input "4886|623815186100858742026272768|1211287002856063997313152"
def inputClause4887 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4887 (by decide) v hb
mask_input "4887|623815167654114668316721280|1211305449600137706864640"
def inputClause4888 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inputList4888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4888 (by decide) v hb
mask_input "4888|623815167654114668316721152|1211305449600137706864768"
def inputClause4889 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4889 (by decide) v hb
mask_input "4889|623808102551134437558452352|1218370552580368465133568"
def inputClause4890 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4890 (by decide) v hb
mask_input "4890|623808102551134437558452224|1218370552580368465133696"
def inputClause4891 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4891 (by decide) v hb
mask_input "4891|623808084104390363848900736|1218388999324442174685184"
def inputClause4892 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4892 (by decide) v hb
mask_input "4892|623808084104390363848900608|1218388999324442174685312"
def inputClause4893 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4893 (by decide) v hb
mask_input "4893|623805741367893002735845504|1220731735821803287740416"
def inputClause4894 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4894 (by decide) v hb
mask_input "4894|623805741367893002735845376|1220731735821803287740544"
def inputClause4895 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4895 (by decide) v hb
mask_input "4895|623805722921148929026293888|1220750182565876997292032"
def inputClause4896 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inputList4896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4896 (by decide) v hb
mask_input "4896|623805722921148929026293760|1220750182565876997292160"
def inputClause4897 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4897 (by decide) v hb
mask_input "4897|620190769825256289324761216|4835703278458516698824704"
def inputClause4898 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4898 (by decide) v hb
mask_input "4898|620190769825256289324761088|4835703278458516698824832"
end Percolation.MaskChain
