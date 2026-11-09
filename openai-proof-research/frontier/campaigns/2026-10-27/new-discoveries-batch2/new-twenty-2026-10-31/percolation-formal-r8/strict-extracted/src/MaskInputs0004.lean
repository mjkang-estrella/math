import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause370 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,false),(24,true),(30,true)]
theorem inputList370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause370 (by decide) v hb
mask_input "370|14680064|147573952590767980544"
def inputClause371 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,false),(24,true),(30,true)]
theorem inputList371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause371 (by decide) v hb
mask_input "371|13631488|147573952590769029120"
def inputClause372 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,true),(30,true)]
theorem inputList372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause372 (by decide) v hb
mask_input "372|12582912|147573952590770077696"
def inputClause373 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,false),(24,true),(30,true)]
theorem inputList373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause373 (by decide) v hb
mask_input "373|11534336|147573952590771126272"
def inputClause374 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,false),(24,true),(30,true)]
theorem inputList374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause374 (by decide) v hb
mask_input "374|10485760|147573952590772174848"
def inputClause375 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,false),(24,true),(30,true)]
theorem inputList375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause375 (by decide) v hb
mask_input "375|9437184|147573952590773223424"
def inputClause376 : CNF.NClause := [(67,false),(20,true),(21,true),(22,true),(23,false),(24,true),(30,true)]
theorem inputList376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause376 (by decide) v hb
mask_input "376|147573952589684801536|1097859072"
def inputClause377 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,true),(24,true),(30,true)]
theorem inputList377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause377 (by decide) v hb
mask_input "377|7340032|147573952590775320576"
def inputClause378 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,true),(24,true),(30,true)]
theorem inputList378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause378 (by decide) v hb
mask_input "378|6291456|147573952590776369152"
def inputClause379 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,true),(24,true),(30,true)]
theorem inputList379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause379 (by decide) v hb
mask_input "379|5242880|147573952590777417728"
def inputClause380 : CNF.NClause := [(67,false),(20,true),(21,true),(22,false),(23,true),(24,true),(30,true)]
theorem inputList380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause380 (by decide) v hb
mask_input "380|147573952589680607232|1102053376"
def inputClause381 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,true),(24,true),(30,true)]
theorem inputList381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause381 (by decide) v hb
mask_input "381|3145728|147573952590779514880"
def inputClause382 : CNF.NClause := [(67,false),(20,true),(21,false),(22,true),(23,true),(24,true),(30,true)]
theorem inputList382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause382 (by decide) v hb
mask_input "382|147573952589678510080|1104150528"
def inputClause383 : CNF.NClause := [(67,false),(20,false),(21,true),(22,true),(23,true),(24,true),(30,true)]
theorem inputList383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) inputClause383 (by decide) v hb
mask_input "383|147573952589677461504|1105199104"
def inputClause385 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,false),(29,false)]
theorem inputList385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause385 (by decide) v hb
mask_input "385|537989392|295147905179352825856"
def inputClause386 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,false),(29,false)]
theorem inputList386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause386 (by decide) v hb
mask_input "386|537989376|295147905179352825872"
def inputClause387 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,false),(29,false)]
theorem inputList387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause387 (by decide) v hb
mask_input "387|537989136|295147905179352826112"
def inputClause388 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,false),(29,false)]
theorem inputList388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause388 (by decide) v hb
mask_input "388|537989120|295147905179352826128"
def inputClause389 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,false),(29,false)]
theorem inputList389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause389 (by decide) v hb
mask_input "389|537985296|295147905179352829952"
def inputClause390 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,false),(29,false)]
theorem inputList390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause390 (by decide) v hb
mask_input "390|537985280|295147905179352829968"
def inputClause391 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,false),(29,false)]
theorem inputList391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause391 (by decide) v hb
mask_input "391|537985040|295147905179352830208"
def inputClause392 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,false),(29,false)]
theorem inputList392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause392 (by decide) v hb
mask_input "392|537985024|295147905179352830224"
def inputClause393 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,false),(29,false)]
theorem inputList393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause393 (by decide) v hb
mask_input "393|537923856|295147905179352891392"
def inputClause394 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,false),(29,false)]
theorem inputList394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause394 (by decide) v hb
mask_input "394|537923840|295147905179352891408"
def inputClause395 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,false),(29,false)]
theorem inputList395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause395 (by decide) v hb
mask_input "395|537923600|295147905179352891648"
def inputClause396 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,false),(29,false)]
theorem inputList396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause396 (by decide) v hb
mask_input "396|537923584|295147905179352891664"
def inputClause397 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,false),(29,false)]
theorem inputList397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause397 (by decide) v hb
mask_input "397|537919760|295147905179352895488"
def inputClause398 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,true),(20,false),(29,false)]
theorem inputList398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause398 (by decide) v hb
mask_input "398|537919744|295147905179352895504"
def inputClause399 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,false),(29,false)]
theorem inputList399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause399 (by decide) v hb
mask_input "399|537919504|295147905179352895744"
def inputClause400 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,true),(20,false),(29,false)]
theorem inputList400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause400 (by decide) v hb
mask_input "400|537919488|295147905179352895760"
def inputClause401 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,true),(29,false)]
theorem inputList401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause401 (by decide) v hb
mask_input "401|536940816|295147905179353874432"
def inputClause402 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,true),(29,false)]
theorem inputList402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause402 (by decide) v hb
mask_input "402|536940800|295147905179353874448"
def inputClause403 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,true),(29,false)]
theorem inputList403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause403 (by decide) v hb
mask_input "403|536940560|295147905179353874688"
def inputClause404 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,true),(29,false)]
theorem inputList404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause404 (by decide) v hb
mask_input "404|536940544|295147905179353874704"
def inputClause405 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,true),(29,false)]
theorem inputList405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause405 (by decide) v hb
mask_input "405|536936720|295147905179353878528"
def inputClause406 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,true),(29,false)]
theorem inputList406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause406 (by decide) v hb
mask_input "406|536936704|295147905179353878544"
def inputClause407 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,true),(29,false)]
theorem inputList407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause407 (by decide) v hb
mask_input "407|536936464|295147905179353878784"
def inputClause408 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,true),(29,false)]
theorem inputList408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause408 (by decide) v hb
mask_input "408|536936448|295147905179353878800"
def inputClause409 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,true),(29,false)]
theorem inputList409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause409 (by decide) v hb
mask_input "409|536875280|295147905179353939968"
def inputClause410 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,true),(29,false)]
theorem inputList410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) inputClause410 (by decide) v hb
mask_input "410|536875264|295147905179353939984"
end Percolation.MaskChain
