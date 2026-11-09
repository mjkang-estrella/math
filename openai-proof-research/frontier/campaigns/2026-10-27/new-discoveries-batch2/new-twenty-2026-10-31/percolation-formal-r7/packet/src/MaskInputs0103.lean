import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7535 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7535 (by decide) v hb
mask_input "7535|302231743134033579606016|657731798641580562496618496"
def inputClause7536 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inputList7536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7536 (by decide) v hb
mask_input "7536|302231743134033445388288|657731798641580562630836224"
def inputClause7537 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7537 (by decide) v hb
mask_input "7537|76153059452667742388224|657957877325261928333836288"
def inputClause7538 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7538 (by decide) v hb
mask_input "7538|76153059452667608170496|657957877325261928468054016"
def inputClause7539 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7539 (by decide) v hb
mask_input "7539|76148447766649315000320|657957881936947946761224192"
def inputClause7540 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7540 (by decide) v hb
mask_input "7540|76148447766649180782592|657957881936947946895441920"
def inputClause7541 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7541 (by decide) v hb
mask_input "7541|75562763642309036736512|657958467621072287039488000"
def inputClause7542 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7542 (by decide) v hb
mask_input "7542|75562763642308902518784|657958467621072287173705728"
def inputClause7543 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7543 (by decide) v hb
mask_input "7543|75558151956290609348608|657958472232758305466875904"
def inputClause7544 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inputList7544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7544 (by decide) v hb
mask_input "7544|75558151956290475130880|657958472232758305601093632"
def inputClause7545 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,true),(89,true)]
theorem inputList7545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7545 (by decide) v hb
mask_input "7545|595195726753418969088|658033435188987842657255424"
def inputClause7546 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,true),(89,true)]
theorem inputList7546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7546 (by decide) v hb
mask_input "7546|595195726753284751360|658033435188987842791473152"
def inputClause7548 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,true),(89,true)]
theorem inputList7548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7548 (by decide) v hb
mask_input "7548|590584040734857363456|658033439800673861218861056"
def inputClause7549 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,true),(89,true)]
theorem inputList7549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7549 (by decide) v hb
mask_input "7549|4899916394713317376|658034025484798201362907136"
def inputClause7550 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,true),(89,true)]
theorem inputList7550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7550 (by decide) v hb
mask_input "7550|4899916394579099648|658034025484798201497124864"
def inputClause7552 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,true),(89,true)]
theorem inputList7552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7552 (by decide) v hb
mask_input "7552|288230376151711744|658034030096484219924512768"
def inputClause7556 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7556 (by decide) v hb
mask_input "7556|1259711329939490809048989696|4611686018695823360"
def inputClause7620 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inputList7620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7620 (by decide) v hb
mask_input "7620|21771290654110534149865472|1237940043897066293594947584"
def inputClause7628 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inputList7628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7628 (by decide) v hb
mask_input "7628|21761845921144794859438080|1237949488630032032885374976"
def inputClause7636 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inputList7636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7636 (by decide) v hb
mask_input "7636|19353439014881275800453120|1240357895536295551944359936"
def inputClause7644 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inputList7644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7644 (by decide) v hb
mask_input "7644|19343994281915536510025728|1240367340269261291234787328"
def inputClause7652 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inputList7652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7652 (by decide) v hb
mask_input "7652|2428477540276467354566656|1257282857010900360390246400"
def inputClause7660 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inputList7660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7660 (by decide) v hb
mask_input "7660|2419032807310728064139264|1257292301743866099680673792"
def inputClause7668 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inputList7668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7668 (by decide) v hb
mask_input "7668|10625901047209005154304|1259700708650129618739658752"
def inputClause7676 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,true),(90,true)]
theorem inputList7676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7676 (by decide) v hb
mask_input "7676|1181168081469714726912|1259710153383095358030086144"
def inputClause7682 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7682 (by decide) v hb
mask_input "7682|388084378474740146048598016|536870912"
def inputClause7683 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7683 (by decide) v hb
mask_input "7683|388084373863054128158081024|4611686018427387904"
def inputClause7684 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7684 (by decide) v hb
mask_input "7684|388084373863054127621210112|4611686018964258816"
def inputClause7685 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7685 (by decide) v hb
mask_input "7685|388084083326834967232643072|295147905179352825856"
def inputClause7686 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7686 (by decide) v hb
mask_input "7686|388084083326834966695772160|295147905179889696768"
def inputClause7687 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7687 (by decide) v hb
mask_input "7687|388084078715148948805255168|299759591197780213760"
def inputClause7688 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inputList7688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7688 (by decide) v hb
mask_input "7688|388084078715148948268384256|299759591198317084672"
def inputClause7689 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7689 (by decide) v hb
mask_input "7689|388065489008808668004614144|18889465931478580854784"
def inputClause7690 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7690 (by decide) v hb
mask_input "7690|388065489008808667467743232|18889465931479117725696"
def inputClause7691 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7691 (by decide) v hb
mask_input "7691|388065484397122649577226240|18894077617497008242688"
def inputClause7692 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7692 (by decide) v hb
mask_input "7692|388065484397122649040355328|18894077617497545113600"
def inputClause7693 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7693 (by decide) v hb
mask_input "7693|388065193860903488651788288|19184613836657933680640"
def inputClause7694 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7694 (by decide) v hb
mask_input "7694|388065193860903488114917376|19184613836658470551552"
def inputClause7695 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7695 (by decide) v hb
mask_input "7695|388065189249217470224400384|19189225522676361068544"
def inputClause7696 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inputList7696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7696 (by decide) v hb
mask_input "7696|388065189249217469687529472|19189225522676897939456"
end Percolation.MaskChain
