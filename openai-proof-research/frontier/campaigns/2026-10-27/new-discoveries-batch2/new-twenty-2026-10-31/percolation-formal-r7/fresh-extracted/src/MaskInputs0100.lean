import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7324 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inputList7324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7324 (by decide) v hb
mask_input "7324|2485553846455034206094360576|642246453356290243559424"
def inputClause7332 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inputList7332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7332 (by decide) v hb
mask_input "7332|2476524681739787444445773824|9671411168603051892146176"
def inputClause7340 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inputList7340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7340 (by decide) v hb
mask_input "7340|2476486902807924487284064256|9709190100466009053855744"
def inputClause7348 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7348 (by decide) v hb
mask_input "7348|2475920218829980129858420736|10275874078410366479499264"
def inputClause7356 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7356 (by decide) v hb
mask_input "7356|2475882439898117172696711168|10313653010273323641208832"
def inputClause7364 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7364 (by decide) v hb
mask_input "7364|10316009725943928045174784|2475880083182446568292745216"
def inputClause7372 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7372 (by decide) v hb
mask_input "7372|10278230794080970883465216|2475917862114309525454454784"
def inputClause7380 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7380 (by decide) v hb
mask_input "7380|9711546816136613457821696|2476484546092253882880098304"
def inputClause7388 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inputList7388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7388 (by decide) v hb
mask_input "7388|9673767884273656296112128|2476522325024116840041807872"
def inputClause7396 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7396 (by decide) v hb
mask_input "7396|644603169026894647525376|2485551489739363601690394624"
def inputClause7404 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,true),(91,true)]
theorem inputList7404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7404 (by decide) v hb
mask_input "7404|606824237163937485815808|2485589268671226558852104192"
def inputClause7412 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inputList7412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7412 (by decide) v hb
mask_input "7412|40140259219580060172288|2486155952649170916277747712"
def inputClause7420 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inputList7420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7420 (by decide) v hb
mask_input "7420|2361327356622898462720|2486193731581033873439457280"
def inputClause7426 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7426 (by decide) v hb
mask_input "7426|658034030384714595942006784|134217728"
def inputClause7427 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7427 (by decide) v hb
mask_input "7427|658034025773028577648836608|4611686018427387904"
def inputClause7428 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7428 (by decide) v hb
mask_input "7428|658034025773028577514618880|4611686018561605632"
def inputClause7429 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7429 (by decide) v hb
mask_input "7429|658033440088904237370572800|590295810358705651712"
def inputClause7430 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7430 (by decide) v hb
mask_input "7430|658033440088904237236355072|590295810358839869440"
def inputClause7431 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7431 (by decide) v hb
mask_input "7431|658033435477218218943184896|594907496377133039616"
def inputClause7432 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7432 (by decide) v hb
mask_input "7432|658033435477218218808967168|594907496377267257344"
def inputClause7433 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7433 (by decide) v hb
mask_input "7433|657958472520988681752805376|75557863725914323419136"
def inputClause7434 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7434 (by decide) v hb
mask_input "7434|657958472520988681618587648|75557863725914457636864"
def inputClause7435 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7435 (by decide) v hb
mask_input "7435|657958467909302663325417472|75562475411932750807040"
def inputClause7436 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7436 (by decide) v hb
mask_input "7436|657958467909302663191199744|75562475411932885024768"
def inputClause7437 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7437 (by decide) v hb
mask_input "7437|657957882225178323047153664|76148159536273029070848"
def inputClause7438 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7438 (by decide) v hb
mask_input "7438|657957882225178322912935936|76148159536273163288576"
def inputClause7439 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7439 (by decide) v hb
mask_input "7439|657957877613492304619765760|76152771222291456458752"
def inputClause7440 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inputList7440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7440 (by decide) v hb
mask_input "7440|657957877613492304485548032|76152771222291590676480"
def inputClause7441 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7441 (by decide) v hb
mask_input "7441|657731798929810938782547968|302231454903657293676544"
def inputClause7442 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7442 (by decide) v hb
mask_input "7442|657731798929810938648330240|302231454903657427894272"
def inputClause7443 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7443 (by decide) v hb
mask_input "7443|657731794318124920355160064|302236066589675721064448"
def inputClause7444 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7444 (by decide) v hb
mask_input "7444|657731794318124920220942336|302236066589675855282176"
def inputClause7445 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7445 (by decide) v hb
mask_input "7445|657731208634000580076896256|302821750714015999328256"
def inputClause7446 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7446 (by decide) v hb
mask_input "7446|657731208634000579942678528|302821750714016133545984"
def inputClause7447 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7447 (by decide) v hb
mask_input "7447|657731204022314561649508352|302826362400034426716160"
def inputClause7448 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inputList7448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7448 (by decide) v hb
mask_input "7448|657731204022314561515290624|302826362400034560933888"
def inputClause7449 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7449 (by decide) v hb
mask_input "7449|657656241066085024459128832|377789318629571617095680"
def inputClause7450 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7450 (by decide) v hb
mask_input "7450|657656241066085024324911104|377789318629571751313408"
def inputClause7451 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7451 (by decide) v hb
mask_input "7451|657656236454399006031740928|377793930315590044483584"
def inputClause7452 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7452 (by decide) v hb
mask_input "7452|657656236454399005897523200|377793930315590178701312"
end Percolation.MaskChain
