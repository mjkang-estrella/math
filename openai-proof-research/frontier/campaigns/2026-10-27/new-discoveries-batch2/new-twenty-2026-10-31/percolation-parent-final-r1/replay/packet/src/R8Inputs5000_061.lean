import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7342 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inputList7342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7342 (by decide) v hb
mask_input "7342|2476484546236369070888845312|9711546672021425449074688"
def inputClause7343 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inputList7343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7343 (by decide) v hb
mask_input "7343|2476484541624683052528566272|9711551283707443809353728"
def inputClause7344 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inputList7344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7344 (by decide) v hb
mask_input "7344|2476484541624683052461457408|9711551283707443876462592"
def inputClause7345 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7345 (by decide) v hb
mask_input "7345|2475920223441666148352917504|10275869466724347985002496"
def inputClause7346 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7346 (by decide) v hb
mask_input "7346|2475920223441666148285808640|10275869466724348052111360"
def inputClause7347 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7347 (by decide) v hb
mask_input "7347|2475920218829980129925529600|10275874078410366412390400"
def inputClause7349 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7349 (by decide) v hb
mask_input "7349|2475917862258424713530310656|10278230649965782807609344"
def inputClause7350 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7350 (by decide) v hb
mask_input "7350|2475917862258424713463201792|10278230649965782874718208"
def inputClause7351 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7351 (by decide) v hb
mask_input "7351|2475917857646738695102922752|10278235261651801234997248"
def inputClause7352 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inputList7352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7352 (by decide) v hb
mask_input "7352|2475917857646738695035813888|10278235261651801302106112"
def inputClause7353 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7353 (by decide) v hb
mask_input "7353|2475882444509803191191207936|10313648398587305146712064"
def inputClause7354 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7354 (by decide) v hb
mask_input "7354|2475882444509803191124099072|10313648398587305213820928"
def inputClause7355 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7355 (by decide) v hb
mask_input "7355|2475882439898117172763820032|10313653010273323574099968"
def inputClause7357 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7357 (by decide) v hb
mask_input "7357|2475880083326561756368601088|10316009581828739969318912"
def inputClause7358 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7358 (by decide) v hb
mask_input "7358|2475880083326561756301492224|10316009581828740036427776"
def inputClause7359 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7359 (by decide) v hb
mask_input "7359|2475880078714875737941213184|10316014193514758396706816"
def inputClause7360 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inputList7360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7360 (by decide) v hb
mask_input "7360|2475880078714875737874104320|10316014193514758463815680"
def inputClause7361 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7361 (by decide) v hb
mask_input "7361|10316014337629946539671552|2475880078570760549798248448"
def inputClause7362 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7362 (by decide) v hb
mask_input "7362|10316014337629946472562688|2475880078570760549865357312"
def inputClause7363 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7363 (by decide) v hb
mask_input "7363|10316009725943928112283648|2475880083182446568225636352"
def inputClause7365 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7365 (by decide) v hb
mask_input "7365|10313653154388511717064704|2475882439754001984620855296"
def inputClause7366 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7366 (by decide) v hb
mask_input "7366|10313653154388511649955840|2475882439754001984687964160"
def inputClause7367 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7367 (by decide) v hb
mask_input "7367|10313648542702493289676800|2475882444365688003048243200"
def inputClause7368 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inputList7368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7368 (by decide) v hb
mask_input "7368|10313648542702493222567936|2475882444365688003115352064"
def inputClause7369 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7369 (by decide) v hb
mask_input "7369|10278235405766989377961984|2475917857502623506959958016"
def inputClause7370 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7370 (by decide) v hb
mask_input "7370|10278235405766989310853120|2475917857502623507027066880"
def inputClause7371 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7371 (by decide) v hb
mask_input "7371|10278230794080970950574080|2475917862114309525387345920"
def inputClause7373 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7373 (by decide) v hb
mask_input "7373|10275874222525554555355136|2475920218685864941782564864"
def inputClause7374 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7374 (by decide) v hb
mask_input "7374|10275874222525554488246272|2475920218685864941849673728"
def inputClause7375 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7375 (by decide) v hb
mask_input "7375|10275869610839536127967232|2475920223297550960209952768"
def inputClause7376 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inputList7376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7376 (by decide) v hb
mask_input "7376|10275869610839536060858368|2475920223297550960277061632"
def inputClause7377 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7377 (by decide) v hb
mask_input "7377|9711551427822631952318464|2476484541480567864385601536"
def inputClause7378 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7378 (by decide) v hb
mask_input "7378|9711551427822631885209600|2476484541480567864452710400"
def inputClause7379 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7379 (by decide) v hb
mask_input "7379|9711546816136613524930560|2476484546092253882812989440"
def inputClause7381 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7381 (by decide) v hb
mask_input "7381|9709190244581197129711616|2476486902663809299208208384"
def inputClause7382 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7382 (by decide) v hb
mask_input "7382|9709190244581197062602752|2476486902663809299275317248"
def inputClause7383 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7383 (by decide) v hb
mask_input "7383|9709185632895178702323712|2476486907275495317635596288"
def inputClause7384 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inputList7384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7384 (by decide) v hb
mask_input "7384|9709185632895178635214848|2476486907275495317702705152"
def inputClause7385 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inputList7385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7385 (by decide) v hb
mask_input "7385|9673772495959674790608896|2476522320412430821547311104"
def inputClause7386 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inputList7386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7386 (by decide) v hb
mask_input "7386|9673772495959674723500032|2476522320412430821614419968"
end Percolation.MaskChain
