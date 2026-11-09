import Inputs045
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14294 : CNF.NClause := [(17,true),(19,true),(670,false)]
theorem inp_14294 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14294 := by
  apply holds_decode v cl_14294
  have he : decodeClause cl_14294 = containClause5 17 19 := by decide
  rw [he]
  exact input_contain 17 19 (by decide) v h
def cl_14295 : CNF.NClause := [(17,true),(20,true),(671,false)]
theorem inp_14295 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14295 := by
  apply holds_decode v cl_14295
  have he : decodeClause cl_14295 = containClause5 17 20 := by decide
  rw [he]
  exact input_contain 17 20 (by decide) v h
def cl_14296 : CNF.NClause := [(17,true),(21,true),(672,false)]
theorem inp_14296 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14296 := by
  apply holds_decode v cl_14296
  have he : decodeClause cl_14296 = containClause5 17 21 := by decide
  rw [he]
  exact input_contain 17 21 (by decide) v h
def cl_14297 : CNF.NClause := [(17,true),(22,true),(673,false)]
theorem inp_14297 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14297 := by
  apply holds_decode v cl_14297
  have he : decodeClause cl_14297 = containClause5 17 22 := by decide
  rw [he]
  exact input_contain 17 22 (by decide) v h
def cl_14298 : CNF.NClause := [(17,true),(23,true),(674,false)]
theorem inp_14298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14298 := by
  apply holds_decode v cl_14298
  have he : decodeClause cl_14298 = containClause5 17 23 := by decide
  rw [he]
  exact input_contain 17 23 (by decide) v h
def cl_14304 : CNF.NClause := [(17,true),(29,true),(680,false)]
theorem inp_14304 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14304 := by
  apply holds_decode v cl_14304
  have he : decodeClause cl_14304 = containClause5 17 29 := by decide
  rw [he]
  exact input_contain 17 29 (by decide) v h
def cl_14305 : CNF.NClause := [(17,true),(30,true),(681,false)]
theorem inp_14305 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14305 := by
  apply holds_decode v cl_14305
  have he : decodeClause cl_14305 = containClause5 17 30 := by decide
  rw [he]
  exact input_contain 17 30 (by decide) v h
def cl_14308 : CNF.NClause := [(18,true),(2,true),(684,false)]
theorem inp_14308 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14308 := by
  apply holds_decode v cl_14308
  have he : decodeClause cl_14308 = containClause5 18 2 := by decide
  rw [he]
  exact input_contain 18 2 (by decide) v h
def cl_14312 : CNF.NClause := [(18,true),(6,true),(688,false)]
theorem inp_14312 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14312 := by
  apply holds_decode v cl_14312
  have he : decodeClause cl_14312 = containClause5 18 6 := by decide
  rw [he]
  exact input_contain 18 6 (by decide) v h
def cl_14316 : CNF.NClause := [(18,true),(10,true),(692,false)]
theorem inp_14316 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14316 := by
  apply holds_decode v cl_14316
  have he : decodeClause cl_14316 = containClause5 18 10 := by decide
  rw [he]
  exact input_contain 18 10 (by decide) v h
def cl_14328 : CNF.NClause := [(18,true),(23,true),(705,false)]
theorem inp_14328 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14328 := by
  apply holds_decode v cl_14328
  have he : decodeClause cl_14328 = containClause5 18 23 := by decide
  rw [he]
  exact input_contain 18 23 (by decide) v h
def cl_14340 : CNF.NClause := [(19,true),(4,true),(717,false)]
theorem inp_14340 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14340 := by
  apply holds_decode v cl_14340
  have he : decodeClause cl_14340 = containClause5 19 4 := by decide
  rw [he]
  exact input_contain 19 4 (by decide) v h
def cl_14343 : CNF.NClause := [(19,true),(7,true),(720,false)]
theorem inp_14343 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14343 := by
  apply holds_decode v cl_14343
  have he : decodeClause cl_14343 = containClause5 19 7 := by decide
  rw [he]
  exact input_contain 19 7 (by decide) v h
def cl_14345 : CNF.NClause := [(19,true),(9,true),(722,false)]
theorem inp_14345 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14345 := by
  apply holds_decode v cl_14345
  have he : decodeClause cl_14345 = containClause5 19 9 := by decide
  rw [he]
  exact input_contain 19 9 (by decide) v h
def cl_14350 : CNF.NClause := [(19,true),(14,true),(727,false)]
theorem inp_14350 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14350 := by
  apply holds_decode v cl_14350
  have he : decodeClause cl_14350 = containClause5 19 14 := by decide
  rw [he]
  exact input_contain 19 14 (by decide) v h
def cl_14352 : CNF.NClause := [(19,true),(16,true),(729,false)]
theorem inp_14352 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14352 := by
  apply holds_decode v cl_14352
  have he : decodeClause cl_14352 = containClause5 19 16 := by decide
  rw [he]
  exact input_contain 19 16 (by decide) v h
def cl_14358 : CNF.NClause := [(19,true),(23,true),(736,false)]
theorem inp_14358 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14358 := by
  apply holds_decode v cl_14358
  have he : decodeClause cl_14358 = containClause5 19 23 := by decide
  rw [he]
  exact input_contain 19 23 (by decide) v h
def cl_14359 : CNF.NClause := [(19,true),(24,true),(737,false)]
theorem inp_14359 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14359 := by
  apply holds_decode v cl_14359
  have he : decodeClause cl_14359 = containClause5 19 24 := by decide
  rw [he]
  exact input_contain 19 24 (by decide) v h
def cl_14362 : CNF.NClause := [(19,true),(27,true),(740,false)]
theorem inp_14362 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14362 := by
  apply holds_decode v cl_14362
  have he : decodeClause cl_14362 = containClause5 19 27 := by decide
  rw [he]
  exact input_contain 19 27 (by decide) v h
def cl_14396 : CNF.NClause := [(21,true),(0,true),(775,false)]
theorem inp_14396 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14396 := by
  apply holds_decode v cl_14396
  have he : decodeClause cl_14396 = containClause5 21 0 := by decide
  rw [he]
  exact input_contain 21 0 (by decide) v h
def cl_14397 : CNF.NClause := [(21,true),(1,true),(776,false)]
theorem inp_14397 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14397 := by
  apply holds_decode v cl_14397
  have he : decodeClause cl_14397 = containClause5 21 1 := by decide
  rw [he]
  exact input_contain 21 1 (by decide) v h
def cl_14398 : CNF.NClause := [(21,true),(2,true),(777,false)]
theorem inp_14398 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14398 := by
  apply holds_decode v cl_14398
  have he : decodeClause cl_14398 = containClause5 21 2 := by decide
  rw [he]
  exact input_contain 21 2 (by decide) v h
def cl_14401 : CNF.NClause := [(21,true),(5,true),(780,false)]
theorem inp_14401 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14401 := by
  apply holds_decode v cl_14401
  have he : decodeClause cl_14401 = containClause5 21 5 := by decide
  rw [he]
  exact input_contain 21 5 (by decide) v h
def cl_14406 : CNF.NClause := [(21,true),(10,true),(785,false)]
theorem inp_14406 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14406 := by
  apply holds_decode v cl_14406
  have he : decodeClause cl_14406 = containClause5 21 10 := by decide
  rw [he]
  exact input_contain 21 10 (by decide) v h
def cl_14407 : CNF.NClause := [(21,true),(11,true),(786,false)]
theorem inp_14407 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14407 := by
  apply holds_decode v cl_14407
  have he : decodeClause cl_14407 = containClause5 21 11 := by decide
  rw [he]
  exact input_contain 21 11 (by decide) v h
def cl_14412 : CNF.NClause := [(21,true),(16,true),(791,false)]
theorem inp_14412 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14412 := by
  apply holds_decode v cl_14412
  have he : decodeClause cl_14412 = containClause5 21 16 := by decide
  rw [he]
  exact input_contain 21 16 (by decide) v h
def cl_14413 : CNF.NClause := [(21,true),(17,true),(792,false)]
theorem inp_14413 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14413 := by
  apply holds_decode v cl_14413
  have he : decodeClause cl_14413 = containClause5 21 17 := by decide
  rw [he]
  exact input_contain 21 17 (by decide) v h
def cl_14415 : CNF.NClause := [(21,true),(19,true),(794,false)]
theorem inp_14415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14415 := by
  apply holds_decode v cl_14415
  have he : decodeClause cl_14415 = containClause5 21 19 := by decide
  rw [he]
  exact input_contain 21 19 (by decide) v h
def cl_14417 : CNF.NClause := [(21,true),(22,true),(797,false)]
theorem inp_14417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14417 := by
  apply holds_decode v cl_14417
  have he : decodeClause cl_14417 = containClause5 21 22 := by decide
  rw [he]
  exact input_contain 21 22 (by decide) v h
def cl_14419 : CNF.NClause := [(21,true),(24,true),(799,false)]
theorem inp_14419 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14419 := by
  apply holds_decode v cl_14419
  have he : decodeClause cl_14419 = containClause5 21 24 := by decide
  rw [he]
  exact input_contain 21 24 (by decide) v h
def cl_14420 : CNF.NClause := [(21,true),(25,true),(800,false)]
theorem inp_14420 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14420 := by
  apply holds_decode v cl_14420
  have he : decodeClause cl_14420 = containClause5 21 25 := by decide
  rw [he]
  exact input_contain 21 25 (by decide) v h
def cl_14422 : CNF.NClause := [(21,true),(27,true),(802,false)]
theorem inp_14422 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14422 := by
  apply holds_decode v cl_14422
  have he : decodeClause cl_14422 = containClause5 21 27 := by decide
  rw [he]
  exact input_contain 21 27 (by decide) v h
def cl_14423 : CNF.NClause := [(21,true),(28,true),(803,false)]
theorem inp_14423 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14423 := by
  apply holds_decode v cl_14423
  have he : decodeClause cl_14423 = containClause5 21 28 := by decide
  rw [he]
  exact input_contain 21 28 (by decide) v h
def cl_14428 : CNF.NClause := [(22,true),(2,true),(808,false)]
theorem inp_14428 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14428 := by
  apply holds_decode v cl_14428
  have he : decodeClause cl_14428 = containClause5 22 2 := by decide
  rw [he]
  exact input_contain 22 2 (by decide) v h
def cl_14432 : CNF.NClause := [(22,true),(6,true),(812,false)]
theorem inp_14432 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14432 := by
  apply holds_decode v cl_14432
  have he : decodeClause cl_14432 = containClause5 22 6 := by decide
  rw [he]
  exact input_contain 22 6 (by decide) v h
def cl_14436 : CNF.NClause := [(22,true),(10,true),(816,false)]
theorem inp_14436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14436 := by
  apply holds_decode v cl_14436
  have he : decodeClause cl_14436 = containClause5 22 10 := by decide
  rw [he]
  exact input_contain 22 10 (by decide) v h
def cl_14445 : CNF.NClause := [(22,true),(19,true),(825,false)]
theorem inp_14445 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14445 := by
  apply holds_decode v cl_14445
  have he : decodeClause cl_14445 = containClause5 22 19 := by decide
  rw [he]
  exact input_contain 22 19 (by decide) v h
def cl_14446 : CNF.NClause := [(22,true),(20,true),(826,false)]
theorem inp_14446 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14446 := by
  apply holds_decode v cl_14446
  have he : decodeClause cl_14446 = containClause5 22 20 := by decide
  rw [he]
  exact input_contain 22 20 (by decide) v h
def cl_14447 : CNF.NClause := [(22,true),(21,true),(827,false)]
theorem inp_14447 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14447 := by
  apply holds_decode v cl_14447
  have he : decodeClause cl_14447 = containClause5 22 21 := by decide
  rw [he]
  exact input_contain 22 21 (by decide) v h
def cl_14449 : CNF.NClause := [(22,true),(24,true),(830,false)]
theorem inp_14449 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14449 := by
  apply holds_decode v cl_14449
  have he : decodeClause cl_14449 = containClause5 22 24 := by decide
  rw [he]
  exact input_contain 22 24 (by decide) v h
def cl_14454 : CNF.NClause := [(22,true),(29,true),(835,false)]
theorem inp_14454 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14454 := by
  apply holds_decode v cl_14454
  have he : decodeClause cl_14454 = containClause5 22 29 := by decide
  rw [he]
  exact input_contain 22 29 (by decide) v h
def cl_14455 : CNF.NClause := [(22,true),(30,true),(836,false)]
theorem inp_14455 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14455 := by
  apply holds_decode v cl_14455
  have he : decodeClause cl_14455 = containClause5 22 30 := by decide
  rw [he]
  exact input_contain 22 30 (by decide) v h
def cl_14578 : CNF.NClause := [(27,true),(2,true),(963,false)]
theorem inp_14578 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14578 := by
  apply holds_decode v cl_14578
  have he : decodeClause cl_14578 = containClause5 27 2 := by decide
  rw [he]
  exact input_contain 27 2 (by decide) v h
def cl_14584 : CNF.NClause := [(27,true),(8,true),(969,false)]
theorem inp_14584 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14584 := by
  apply holds_decode v cl_14584
  have he : decodeClause cl_14584 = containClause5 27 8 := by decide
  rw [he]
  exact input_contain 27 8 (by decide) v h
def cl_14590 : CNF.NClause := [(27,true),(14,true),(975,false)]
theorem inp_14590 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14590 := by
  apply holds_decode v cl_14590
  have he : decodeClause cl_14590 = containClause5 27 14 := by decide
  rw [he]
  exact input_contain 27 14 (by decide) v h
def cl_14597 : CNF.NClause := [(27,true),(21,true),(982,false)]
theorem inp_14597 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14597 := by
  apply holds_decode v cl_14597
  have he : decodeClause cl_14597 = containClause5 27 21 := by decide
  rw [he]
  exact input_contain 27 21 (by decide) v h
def cl_14602 : CNF.NClause := [(27,true),(26,true),(987,false)]
theorem inp_14602 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14602 := by
  apply holds_decode v cl_14602
  have he : decodeClause cl_14602 = containClause5 27 26 := by decide
  rw [he]
  exact input_contain 27 26 (by decide) v h
def cl_14606 : CNF.NClause := [(28,true),(0,true),(992,false)]
theorem inp_14606 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14606 := by
  apply holds_decode v cl_14606
  have he : decodeClause cl_14606 = containClause5 28 0 := by decide
  rw [he]
  exact input_contain 28 0 (by decide) v h
def cl_14611 : CNF.NClause := [(28,true),(5,true),(997,false)]
theorem inp_14611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14611 := by
  apply holds_decode v cl_14611
  have he : decodeClause cl_14611 = containClause5 28 5 := by decide
  rw [he]
  exact input_contain 28 5 (by decide) v h
def cl_14616 : CNF.NClause := [(28,true),(10,true),(1002,false)]
theorem inp_14616 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14616 := by
  apply holds_decode v cl_14616
  have he : decodeClause cl_14616 = containClause5 28 10 := by decide
  rw [he]
  exact input_contain 28 10 (by decide) v h
end Percolation.Replay
