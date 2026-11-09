import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3339 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,false),(57,false)]
theorem inputList3339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3339 (by decide) v hb
mask_input "3339|162134018991587328|20769187434139310514403529013067776"
def inputClause3340 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,false),(57,false)]
theorem inputList3340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3340 (by decide) v hb
mask_input "3340|162133984631848960|20769187434139310514403563372806144"
def inputClause3341 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,false),(57,false)]
theorem inputList3341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3341 (by decide) v hb
mask_input "3341|162129689664552960|20769187434139310514407858340102144"
def inputClause3342 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,true),(54,false),(57,false)]
theorem inputList3342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3342 (by decide) v hb
mask_input "3342|162129655304814592|20769187434139310514407892699840512"
def inputClause3343 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,true),(54,false),(57,false)]
theorem inputList3343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3343 (by decide) v hb
mask_input "3343|162129620945076224|20769187434139310514407927059578880"
def inputClause3344 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,true),(54,false),(57,false)]
theorem inputList3344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3344 (by decide) v hb
mask_input "3344|162129586585337856|20769187434139310514407961419317248"
def inputClause3345 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,true),(57,false)]
theorem inputList3345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3345 (by decide) v hb
mask_input "3345|144401164178292736|20769187434139310532136383826362368"
def inputClause3346 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,true),(57,false)]
theorem inputList3346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3346 (by decide) v hb
mask_input "3346|144401129818554368|20769187434139310532136418186100736"
def inputClause3347 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,true),(57,false)]
theorem inputList3347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3347 (by decide) v hb
mask_input "3347|144401095458816000|20769187434139310532136452545839104"
def inputClause3348 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,true),(57,false)]
theorem inputList3348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3348 (by decide) v hb
mask_input "3348|144401061099077632|20769187434139310532136486905577472"
def inputClause3349 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,true),(57,false)]
theorem inputList3349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3349 (by decide) v hb
mask_input "3349|144396766131781632|20769187434139310532140781872873472"
def inputClause3350 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,true),(57,false)]
theorem inputList3350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3350 (by decide) v hb
mask_input "3350|144396731772043264|20769187434139310532140816232611840"
def inputClause3351 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,true),(57,false)]
theorem inputList3351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3351 (by decide) v hb
mask_input "3351|144396697412304896|20769187434139310532140850592350208"
def inputClause3352 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,true),(57,false)]
theorem inputList3352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3352 (by decide) v hb
mask_input "3352|144396663052566528|20769187434139310532140884952088576"
def inputClause3353 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,true),(57,false)]
theorem inputList3353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3353 (by decide) v hb
mask_input "3353|144119689201582080|20769187434139310532417858803073024"
def inputClause3354 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,true),(57,false)]
theorem inputList3354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3354 (by decide) v hb
mask_input "3354|144119654841843712|20769187434139310532417893162811392"
def inputClause3355 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,true),(57,false)]
theorem inputList3355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3355 (by decide) v hb
mask_input "3355|144119620482105344|20769187434139310532417927522549760"
def inputClause3356 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,true),(57,false)]
theorem inputList3356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3356 (by decide) v hb
mask_input "3356|144119586122366976|20769187434139310532417961882288128"
def inputClause3357 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,true),(57,false)]
theorem inputList3357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3357 (by decide) v hb
mask_input "3357|144115291155070976|20769187434139310532422256849584128"
def inputClause3358 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,true),(54,true),(57,false)]
theorem inputList3358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3358 (by decide) v hb
mask_input "3358|144115256795332608|20769187434139310532422291209322496"
def inputClause3359 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,true),(54,true),(57,false)]
theorem inputList3359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3359 (by decide) v hb
mask_input "3359|144115222435594240|20769187434139310532422325569060864"
def inputClause3360 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,true),(57,false)]
theorem inputList3360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3360 (by decide) v hb
mask_input "3360|20769187434139310658237173392736256|18300374611918848"
def inputClause3361 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,false),(57,true)]
theorem inputList3361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3361 (by decide) v hb
mask_input "3361|18300374611918848|20769187434139310658237173392736256"
def inputClause3362 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,false),(57,true)]
theorem inputList3362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3362 (by decide) v hb
mask_input "3362|18300340252180480|20769187434139310658237207752474624"
def inputClause3363 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,false),(57,true)]
theorem inputList3363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3363 (by decide) v hb
mask_input "3363|18300305892442112|20769187434139310658237242112212992"
def inputClause3364 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,false),(57,true)]
theorem inputList3364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3364 (by decide) v hb
mask_input "3364|18300271532703744|20769187434139310658237276471951360"
def inputClause3365 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,false),(57,true)]
theorem inputList3365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3365 (by decide) v hb
mask_input "3365|18295976565407744|20769187434139310658241571439247360"
def inputClause3366 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,false),(57,true)]
theorem inputList3366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3366 (by decide) v hb
mask_input "3366|18295942205669376|20769187434139310658241605798985728"
def inputClause3367 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,false),(57,true)]
theorem inputList3367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3367 (by decide) v hb
mask_input "3367|18295907845931008|20769187434139310658241640158724096"
def inputClause3368 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,false),(57,true)]
theorem inputList3368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3368 (by decide) v hb
mask_input "3368|18295873486192640|20769187434139310658241674518462464"
def inputClause3369 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,false),(57,true)]
theorem inputList3369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3369 (by decide) v hb
mask_input "3369|18018899635208192|20769187434139310658518648369446912"
def inputClause3370 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,false),(57,true)]
theorem inputList3370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3370 (by decide) v hb
mask_input "3370|18018865275469824|20769187434139310658518682729185280"
def inputClause3371 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,false),(57,true)]
theorem inputList3371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3371 (by decide) v hb
mask_input "3371|18018830915731456|20769187434139310658518717088923648"
def inputClause3372 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,true),(54,false),(57,true)]
theorem inputList3372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3372 (by decide) v hb
mask_input "3372|18018796555993088|20769187434139310658518751448662016"
def inputClause3373 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,true),(54,false),(57,true)]
theorem inputList3373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3373 (by decide) v hb
mask_input "3373|18014501588697088|20769187434139310658523046415958016"
def inputClause3374 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,true),(54,false),(57,true)]
theorem inputList3374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3374 (by decide) v hb
mask_input "3374|18014467228958720|20769187434139310658523080775696384"
def inputClause3375 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,true),(54,false),(57,true)]
theorem inputList3375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3375 (by decide) v hb
mask_input "3375|18014432869220352|20769187434139310658523115135434752"
def inputClause3377 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,true),(57,true)]
theorem inputList3377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3377 (by decide) v hb
mask_input "3377|285976102436864|20769187434139310676251571902218240"
def inputClause3378 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,true),(57,true)]
theorem inputList3378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3378 (by decide) v hb
mask_input "3378|285941742698496|20769187434139310676251606261956608"
def inputClause3379 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,true),(57,true)]
theorem inputList3379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3379 (by decide) v hb
mask_input "3379|285907382960128|20769187434139310676251640621694976"
end Percolation.MaskChain
