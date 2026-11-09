import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3291 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,true),(61,false)]
theorem inputList3291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3291 (by decide) v hb
mask_input "3291|2305843352811077632|10384593717069655257062779364835328"
def inputClause3293 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,true),(61,false)]
theorem inputList3293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3293 (by decide) v hb
mask_input "3293|2305843215372124160|10384593717069655257062916803788800"
def inputClause3296 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,true),(40,true),(61,false)]
theorem inputList3296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3296 (by decide) v hb
mask_input "3296|10384593717069657562904001872134144|2130303778816"
def inputClause3297 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,false),(61,true)]
theorem inputList3297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3297 (by decide) v hb
mask_input "3297|2130303778816|10384593717069657562904001872134144"
def inputClause3298 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,false),(61,true)]
theorem inputList3298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3298 (by decide) v hb
mask_input "3298|2061584302080|10384593717069657562904070591610880"
def inputClause3299 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,false),(61,true)]
theorem inputList3299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3299 (by decide) v hb
mask_input "3299|1992864825344|10384593717069657562904139311087616"
def inputClause3300 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,false),(61,true)]
theorem inputList3300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3300 (by decide) v hb
mask_input "3300|1924145348608|10384593717069657562904208030564352"
def inputClause3301 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,false),(61,true)]
theorem inputList3301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3301 (by decide) v hb
mask_input "3301|1855425871872|10384593717069657562904276750041088"
def inputClause3302 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,false),(61,true)]
theorem inputList3302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3302 (by decide) v hb
mask_input "3302|1786706395136|10384593717069657562904345469517824"
def inputClause3303 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,false),(61,true)]
theorem inputList3303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3303 (by decide) v hb
mask_input "3303|1717986918400|10384593717069657562904414188994560"
def inputClause3304 : CNF.NClause := [(113,true),(36,true),(37,true),(38,true),(39,false),(40,false),(61,true)]
theorem inputList3304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3304 (by decide) v hb
mask_input "3304|1649267441664|10384593717069657562904482908471296"
def inputClause3305 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,false),(61,true)]
theorem inputList3305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3305 (by decide) v hb
mask_input "3305|1580547964928|10384593717069657562904551627948032"
def inputClause3306 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,false),(61,true)]
theorem inputList3306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3306 (by decide) v hb
mask_input "3306|1511828488192|10384593717069657562904620347424768"
def inputClause3307 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,false),(61,true)]
theorem inputList3307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3307 (by decide) v hb
mask_input "3307|1443109011456|10384593717069657562904689066901504"
def inputClause3308 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,true),(40,false),(61,true)]
theorem inputList3308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3308 (by decide) v hb
mask_input "3308|1374389534720|10384593717069657562904757786378240"
def inputClause3309 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,false),(61,true)]
theorem inputList3309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3309 (by decide) v hb
mask_input "3309|1305670057984|10384593717069657562904826505854976"
def inputClause3310 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,true),(40,false),(61,true)]
theorem inputList3310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3310 (by decide) v hb
mask_input "3310|1236950581248|10384593717069657562904895225331712"
def inputClause3311 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,true),(40,false),(61,true)]
theorem inputList3311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3311 (by decide) v hb
mask_input "3311|1168231104512|10384593717069657562904963944808448"
def inputClause3313 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,false),(40,true),(61,true)]
theorem inputList3313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3313 (by decide) v hb
mask_input "3313|1030792151040|10384593717069657562905101383761920"
def inputClause3314 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,false),(40,true),(61,true)]
theorem inputList3314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3314 (by decide) v hb
mask_input "3314|962072674304|10384593717069657562905170103238656"
def inputClause3315 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,false),(40,true),(61,true)]
theorem inputList3315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3315 (by decide) v hb
mask_input "3315|893353197568|10384593717069657562905238822715392"
def inputClause3316 : CNF.NClause := [(113,true),(36,true),(37,true),(38,false),(39,false),(40,true),(61,true)]
theorem inputList3316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3316 (by decide) v hb
mask_input "3316|824633720832|10384593717069657562905307542192128"
def inputClause3317 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,false),(40,true),(61,true)]
theorem inputList3317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3317 (by decide) v hb
mask_input "3317|755914244096|10384593717069657562905376261668864"
def inputClause3318 : CNF.NClause := [(113,true),(36,true),(37,false),(38,true),(39,false),(40,true),(61,true)]
theorem inputList3318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3318 (by decide) v hb
mask_input "3318|687194767360|10384593717069657562905444981145600"
def inputClause3319 : CNF.NClause := [(113,true),(36,false),(37,true),(38,true),(39,false),(40,true),(61,true)]
theorem inputList3319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3319 (by decide) v hb
mask_input "3319|618475290624|10384593717069657562905513700622336"
def inputClause3321 : CNF.NClause := [(113,true),(36,false),(37,false),(38,false),(39,true),(40,true),(61,true)]
theorem inputList3321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3321 (by decide) v hb
mask_input "3321|481036337152|10384593717069657562905651139575808"
def inputClause3322 : CNF.NClause := [(113,true),(36,true),(37,false),(38,false),(39,true),(40,true),(61,true)]
theorem inputList3322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3322 (by decide) v hb
mask_input "3322|412316860416|10384593717069657562905719859052544"
def inputClause3323 : CNF.NClause := [(113,true),(36,false),(37,true),(38,false),(39,true),(40,true),(61,true)]
theorem inputList3323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3323 (by decide) v hb
mask_input "3323|343597383680|10384593717069657562905788578529280"
def inputClause3325 : CNF.NClause := [(113,true),(36,false),(37,false),(38,true),(39,true),(40,true),(61,true)]
theorem inputList3325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3325 (by decide) v hb
mask_input "3325|206158430208|10384593717069657562905926017482752"
def inputClause3328 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,true),(40,true),(61,true)]
theorem inputList3328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 20) 20) (activationX_mem 20) inputClause3328 (by decide) v hb
mask_input "3328|10384593717069655257060992658440192|2305845139517472768"
def inputClause3329 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,false),(54,false),(57,false)]
theorem inputList3329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3329 (by decide) v hb
mask_input "3329|162415562687774720|20769187434139310514121985316880384"
def inputClause3330 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,false),(54,false),(57,false)]
theorem inputList3330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3330 (by decide) v hb
mask_input "3330|162415528328036352|20769187434139310514122019676618752"
def inputClause3331 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,false),(57,false)]
theorem inputList3331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3331 (by decide) v hb
mask_input "3331|162415493968297984|20769187434139310514122054036357120"
def inputClause3332 : CNF.NClause := [(114,true),(35,true),(36,true),(42,false),(48,false),(54,false),(57,false)]
theorem inputList3332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3332 (by decide) v hb
mask_input "3332|162415459608559616|20769187434139310514122088396095488"
def inputClause3333 : CNF.NClause := [(114,true),(35,false),(36,false),(42,true),(48,false),(54,false),(57,false)]
theorem inputList3333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3333 (by decide) v hb
mask_input "3333|162411164641263616|20769187434139310514126383363391488"
def inputClause3334 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,false),(57,false)]
theorem inputList3334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3334 (by decide) v hb
mask_input "3334|162411130281525248|20769187434139310514126417723129856"
def inputClause3335 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(54,false),(57,false)]
theorem inputList3335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3335 (by decide) v hb
mask_input "3335|162411095921786880|20769187434139310514126452082868224"
def inputClause3336 : CNF.NClause := [(114,true),(35,true),(36,true),(42,true),(48,false),(54,false),(57,false)]
theorem inputList3336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3336 (by decide) v hb
mask_input "3336|162411061562048512|20769187434139310514126486442606592"
def inputClause3337 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(48,true),(54,false),(57,false)]
theorem inputList3337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3337 (by decide) v hb
mask_input "3337|162134087711064064|20769187434139310514403460293591040"
def inputClause3338 : CNF.NClause := [(114,true),(35,true),(36,false),(42,false),(48,true),(54,false),(57,false)]
theorem inputList3338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 21) 21) (activationX_mem 21) inputClause3338 (by decide) v hb
mask_input "3338|162134053351325696|20769187434139310514403494653329408"
end Percolation.MaskChain
