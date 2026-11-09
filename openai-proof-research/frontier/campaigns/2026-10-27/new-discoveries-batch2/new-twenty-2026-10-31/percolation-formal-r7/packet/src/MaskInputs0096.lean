import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6969 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,true),(89,false)]
theorem inputList6969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6969 (by decide) v hb
mask_input "6969|618970204128145273062948864|12108147662077770327916544"
def inputClause6970 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,true),(89,false)]
theorem inputList6970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6970 (by decide) v hb
mask_input "6970|618970204128145273054560256|12108147662077770336305152"
def inputClause6972 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,true),(89,false)]
theorem inputList6972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6972 (by decide) v hb
mask_input "6972|618970167234657125635457024|12108184555565917755408384"
def inputClause6973 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,true),(89,false)]
theorem inputList6973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6973 (by decide) v hb
mask_input "6973|618970056554192683386535936|12108295236030360004329472"
def inputClause6974 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,true),(89,false)]
theorem inputList6974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6974 (by decide) v hb
mask_input "6974|618970056554192683378147328|12108295236030360012718080"
def inputClause6976 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,true),(89,false)]
theorem inputList6976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6976 (by decide) v hb
mask_input "6976|618970019660704535959044096|12108332129518507431821312"
def inputClause6977 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6977 (by decide) v hb
mask_input "6977|12108332147532905941303296|618970019642690137449562112"
def inputClause6978 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6978 (by decide) v hb
mask_input "6978|12108332147532905932914688|618970019642690137457950720"
def inputClause6979 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6979 (by decide) v hb
mask_input "6979|12108295254044758522200064|618970056536178284868665344"
def inputClause6980 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6980 (by decide) v hb
mask_input "6980|12108295254044758513811456|618970056536178284877053952"
def inputClause6981 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6981 (by decide) v hb
mask_input "6981|12108184573580316264890368|618970167216642727125975040"
def inputClause6982 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6982 (by decide) v hb
mask_input "6982|12108184573580316256501760|618970167216642727134363648"
def inputClause6983 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6983 (by decide) v hb
mask_input "6983|12108147680092168845787136|618970204110130874545078272"
def inputClause6984 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inputList6984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6984 (by decide) v hb
mask_input "6984|12108147680092168837398528|618970204110130874553466880"
def inputClause6985 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6985 (by decide) v hb
mask_input "6985|12089442681601427360448512|618988909108621616030416896"
def inputClause6986 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6986 (by decide) v hb
mask_input "6986|12089442681601427352059904|618988909108621616038805504"
def inputClause6987 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6987 (by decide) v hb
mask_input "6987|12089405788113279941345280|618988946002109763449520128"
def inputClause6988 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6988 (by decide) v hb
mask_input "6988|12089405788113279932956672|618988946002109763457908736"
def inputClause6989 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6989 (by decide) v hb
mask_input "6989|12089295107648837684035584|618989056682574205706829824"
def inputClause6990 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6990 (by decide) v hb
mask_input "6990|12089295107648837675646976|618989056682574205715218432"
def inputClause6991 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6991 (by decide) v hb
mask_input "6991|12089258214160690264932352|618989093576062353125933056"
def inputClause6992 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inputList6992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6992 (by decide) v hb
mask_input "6992|12089258214160690256543744|618989093576062353134321664"
def inputClause6993 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inputList6993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6993 (by decide) v hb
mask_input "6993|9690480508303647591890944|621387871281919395798974464"
def inputClause6994 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inputList6994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6994 (by decide) v hb
mask_input "6994|9690480508303647583502336|621387871281919395807363072"
def inputClause6995 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inputList6995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6995 (by decide) v hb
mask_input "6995|9690443614815500172787712|621387908175407543218077696"
def inputClause6996 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inputList6996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6996 (by decide) v hb
mask_input "6996|9690443614815500164399104|621387908175407543226466304"
def inputClause6997 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inputList6997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6997 (by decide) v hb
mask_input "6997|9690332934351057915478016|621388018855871985475387392"
def inputClause6998 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inputList6998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6998 (by decide) v hb
mask_input "6998|9690332934351057907089408|621388018855871985483776000"
def inputClause6999 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inputList6999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6999 (by decide) v hb
mask_input "6999|9690296040862910496374784|621388055749360132894490624"
def inputClause7000 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inputList7000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7000 (by decide) v hb
mask_input "7000|9690296040862910487986176|621388055749360132902879232"
def inputClause7001 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7001 (by decide) v hb
mask_input "7001|9671591042372169011036160|621406760747850874379829248"
def inputClause7002 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7002 (by decide) v hb
mask_input "7002|9671591042372169002647552|621406760747850874388217856"
def inputClause7003 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7003 (by decide) v hb
mask_input "7003|9671554148884021591932928|621406797641339021798932480"
def inputClause7004 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7004 (by decide) v hb
mask_input "7004|9671554148884021583544320|621406797641339021807321088"
def inputClause7005 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7005 (by decide) v hb
mask_input "7005|9671443468419579334623232|621406908321803464056242176"
def inputClause7006 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7006 (by decide) v hb
mask_input "7006|9671443468419579326234624|621406908321803464064630784"
def inputClause7007 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7007 (by decide) v hb
mask_input "7007|9671406574931431915520000|621406945215291611475345408"
def inputClause7008 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inputList7008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7008 (by decide) v hb
mask_input "7008|9671406574931431907131392|621406945215291611483734016"
def inputClause7009 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7009 (by decide) v hb
mask_input "7009|2436925590615872543653888|628641426199607170847211520"
def inputClause7010 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inputList7010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause7010 (by decide) v hb
mask_input "7010|2436925590615872535265280|628641426199607170855600128"
end Percolation.MaskChain
