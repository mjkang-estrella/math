import NReplay076
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_78343 : CNF.NClause := [(50,false),(77,true),(85,false),(63,false),(90,true)]
theorem der_78343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78343 :=
  CNF.rup_sound cl_78343 [cl_34036,cl_51444] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34036 v h) (hints_cons _ _ _ (der_51444 v h) (by intro d hd; cases hd)))
def cl_78345 : CNF.NClause := [(50,false),(63,true),(19,false),(77,false),(74,false)]
theorem der_78345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78345 :=
  CNF.rup_sound cl_78345 [cl_34046,cl_77201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34046 v h) (hints_cons _ _ _ (der_77201 v h) (by intro d hd; cases hd)))
def cl_78346 : CNF.NClause := [(50,false),(77,false),(63,false),(19,false),(85,true)]
theorem der_78346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78346 :=
  CNF.rup_sound cl_78346 [cl_34055,cl_52611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34055 v h) (hints_cons _ _ _ (der_52611 v h) (by intro d hd; cases hd)))
def cl_78348 : CNF.NClause := [(63,true),(50,false),(90,true),(71,true),(77,false)]
theorem der_78348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78348 :=
  CNF.rup_sound cl_78348 [cl_52612,cl_77205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52612 v h) (hints_cons _ _ _ (der_77205 v h) (by intro d hd; cases hd)))
def cl_78349 : CNF.NClause := [(63,true),(50,false),(19,false),(90,true),(74,false)]
theorem der_78349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78349 :=
  CNF.rup_sound cl_78349 [cl_34059,cl_77205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34059 v h) (hints_cons _ _ _ (der_77205 v h) (by intro d hd; cases hd)))
def cl_78351 : CNF.NClause := [(50,false),(77,true),(19,true),(74,true),(71,true)]
theorem der_78351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78351 :=
  CNF.rup_sound cl_78351 [cl_34071,cl_77199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34071 v h) (hints_cons _ _ _ (der_77199 v h) (by intro d hd; cases hd)))
def cl_78357 : CNF.NClause := [(32,false),(81,true),(1,false),(86,false),(76,false)]
theorem der_78357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78357 :=
  CNF.rup_sound cl_78357 [cl_52621,cl_51495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52621 v h) (hints_cons _ _ _ (der_51495 v h) (by intro d hd; cases hd)))
def cl_78358 : CNF.NClause := [(32,false),(1,true),(76,false),(87,false),(86,false)]
theorem der_78358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78358 :=
  CNF.rup_sound cl_78358 [cl_52622,cl_51477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52622 v h) (hints_cons _ _ _ (der_51477 v h) (by intro d hd; cases hd)))
def cl_78363 : CNF.NClause := [(32,false),(86,true),(81,false),(87,false),(71,false)]
theorem der_78363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78363 :=
  CNF.rup_sound cl_78363 [cl_52632,cl_52627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52632 v h) (hints_cons _ _ _ (der_52627 v h) (by intro d hd; cases hd)))
def cl_78364 : CNF.NClause := [(32,false),(87,false),(76,true),(71,true),(66,false)]
theorem der_78364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78364 :=
  CNF.rup_sound cl_78364 [cl_34092,cl_51481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34092 v h) (hints_cons _ _ _ (der_51481 v h) (by intro d hd; cases hd)))
def cl_78366 : CNF.NClause := [(32,false),(71,true),(87,false),(86,true),(76,true)]
theorem der_78366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78366 :=
  CNF.rup_sound cl_78366 [cl_34094,cl_51481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34094 v h) (hints_cons _ _ _ (der_51481 v h) (by intro d hd; cases hd)))
def cl_78367 : CNF.NClause := [(32,false),(66,false),(71,true),(76,false),(87,false)]
theorem der_78367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78367 :=
  CNF.rup_sound cl_78367 [cl_34097,cl_51477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34097 v h) (hints_cons _ _ _ (der_51477 v h) (by intro d hd; cases hd)))
def cl_78370 : CNF.NClause := [(32,false),(81,true),(66,false),(87,false),(76,true)]
theorem der_78370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78370 :=
  CNF.rup_sound cl_78370 [cl_34102,cl_51481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34102 v h) (hints_cons _ _ _ (der_51481 v h) (by intro d hd; cases hd)))
def cl_78372 : CNF.NClause := [(32,false),(66,true),(81,false),(86,false),(76,false)]
theorem der_78372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78372 :=
  CNF.rup_sound cl_78372 [cl_34112,cl_51488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34112 v h) (hints_cons _ _ _ (der_51488 v h) (by intro d hd; cases hd)))
def cl_78373 : CNF.NClause := [(32,false),(87,true),(71,false),(86,false),(81,false)]
theorem der_78373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78373 :=
  CNF.rup_sound cl_78373 [cl_52636,cl_51482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52636 v h) (hints_cons _ _ _ (der_51482 v h) (by intro d hd; cases hd)))
def cl_78374 : CNF.NClause := [(32,false),(81,false),(76,true),(66,false),(86,false)]
theorem der_78374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78374 :=
  CNF.rup_sound cl_78374 [cl_34115,cl_51483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34115 v h) (hints_cons _ _ _ (der_51483 v h) (by intro d hd; cases hd)))
def cl_78375 : CNF.NClause := [(32,false),(66,true),(71,true),(81,false),(86,false)]
theorem der_78375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78375 :=
  CNF.rup_sound cl_78375 [cl_34117,cl_77216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34117 v h) (hints_cons _ _ _ (der_77216 v h) (by intro d hd; cases hd)))
def cl_78376 : CNF.NClause := [(32,false),(66,true),(76,false),(86,false),(71,false)]
theorem der_78376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78376 :=
  CNF.rup_sound cl_78376 [cl_34119,cl_51485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34119 v h) (hints_cons _ _ _ (der_51485 v h) (by intro d hd; cases hd)))
def cl_78380 : CNF.NClause := [(32,false),(76,true),(86,false),(81,true),(66,false)]
theorem der_78380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78380 :=
  CNF.rup_sound cl_78380 [cl_34126,cl_51486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34126 v h) (hints_cons _ _ _ (der_51486 v h) (by intro d hd; cases hd)))
def cl_78381 : CNF.NClause := [(32,false),(87,true),(1,false),(86,false),(71,false)]
theorem der_78381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78381 :=
  CNF.rup_sound cl_78381 [cl_34127,cl_78373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34127 v h) (hints_cons _ _ _ (der_78373 v h) (by intro d hd; cases hd)))
def cl_78383 : CNF.NClause := [(32,false),(1,true),(81,false),(76,false),(71,false)]
theorem der_78383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78383 :=
  CNF.rup_sound cl_78383 [cl_34133,cl_51488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34133 v h) (hints_cons _ _ _ (der_51488 v h) (by intro d hd; cases hd)))
def cl_78384 : CNF.NClause := [(32,false),(71,true),(1,false),(86,true),(66,false)]
theorem der_78384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78384 :=
  CNF.rup_sound cl_78384 [cl_52639,cl_51497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52639 v h) (hints_cons _ _ _ (der_51497 v h) (by intro d hd; cases hd)))
def cl_78385 : CNF.NClause := [(32,false),(71,true),(76,false),(86,true),(81,false)]
theorem der_78385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78385 :=
  CNF.rup_sound cl_78385 [cl_34136,cl_77217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34136 v h) (hints_cons _ _ _ (der_77217 v h) (by intro d hd; cases hd)))
def cl_78386 : CNF.NClause := [(32,false),(71,false),(66,false),(81,false),(76,true)]
theorem der_78386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78386 :=
  CNF.rup_sound cl_78386 [cl_34140,cl_78374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34140 v h) (hints_cons _ _ _ (der_78374 v h) (by intro d hd; cases hd)))
def cl_78388 : CNF.NClause := [(32,false),(66,true),(87,true),(86,true),(81,false)]
theorem der_78388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78388 :=
  CNF.rup_sound cl_78388 [cl_34146,cl_77217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34146 v h) (hints_cons _ _ _ (der_77217 v h) (by intro d hd; cases hd)))
def cl_78389 : CNF.NClause := [(32,false),(1,false),(86,true),(76,true),(66,false)]
theorem der_78389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78389 :=
  CNF.rup_sound cl_78389 [cl_34154,cl_51497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34154 v h) (hints_cons _ _ _ (der_51497 v h) (by intro d hd; cases hd)))
def cl_78393 : CNF.NClause := [(83,true),(23,true),(26,true),(11,false),(5,false)]
theorem der_78393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78393 :=
  CNF.rup_sound cl_78393 [cl_24543,cl_62292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24543 v h) (hints_cons _ _ _ (der_62292 v h) (by intro d hd; cases hd)))
def cl_78396 : CNF.NClause := [(49,false),(77,true),(65,false),(69,false),(73,false)]
theorem der_78396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78396 :=
  CNF.rup_sound cl_78396 [cl_34296,cl_77561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34296 v h) (hints_cons _ _ _ (der_77561 v h) (by intro d hd; cases hd)))
def cl_78401 : CNF.NClause := [(21,false),(52,false),(88,false),(67,false),(85,true)]
theorem der_78401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78401 :=
  CNF.rup_sound cl_78401 [cl_52649,cl_51767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52649 v h) (hints_cons _ _ _ (der_51767 v h) (by intro d hd; cases hd)))
def cl_78402 : CNF.NClause := [(45,false),(72,false),(79,true),(63,false),(70,false)]
theorem der_78402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78402 :=
  CNF.rup_sound cl_78402 [cl_52652,cl_51577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52652 v h) (hints_cons _ _ _ (der_51577 v h) (by intro d hd; cases hd)))
def cl_78403 : CNF.NClause := [(45,false),(14,true),(86,false),(89,false),(79,true)]
theorem der_78403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78403 :=
  CNF.rup_sound cl_78403 [cl_52653,cl_77367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52653 v h) (hints_cons _ _ _ (der_77367 v h) (by intro d hd; cases hd)))
def cl_78405 : CNF.NClause := [(90,true),(86,false),(67,false),(64,false),(53,false)]
theorem der_78405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78405 :=
  CNF.rup_sound cl_78405 [cl_34314,cl_77397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34314 v h) (hints_cons _ _ _ (der_77397 v h) (by intro d hd; cases hd)))
def cl_78408 : CNF.NClause := [(45,false),(79,false),(89,false),(86,false),(70,true)]
theorem der_78408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78408 :=
  CNF.rup_sound cl_78408 [cl_34321,cl_51884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34321 v h) (hints_cons _ _ _ (der_51884 v h) (by intro d hd; cases hd)))
def cl_78409 : CNF.NClause := [(45,false),(72,true),(70,true),(86,false),(89,false)]
theorem der_78409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78409 :=
  CNF.rup_sound cl_78409 [cl_34323,cl_51884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34323 v h) (hints_cons _ _ _ (der_51884 v h) (by intro d hd; cases hd)))
def cl_78410 : CNF.NClause := [(45,false),(63,false),(86,true),(72,false),(79,false)]
theorem der_78410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78410 :=
  CNF.rup_sound cl_78410 [cl_34324,cl_51588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34324 v h) (hints_cons _ _ _ (der_51588 v h) (by intro d hd; cases hd)))
def cl_78412 : CNF.NClause := [(45,false),(72,false),(86,false),(63,false),(70,true)]
theorem der_78412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78412 :=
  CNF.rup_sound cl_78412 [cl_34328,cl_51584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34328 v h) (hints_cons _ _ _ (der_51584 v h) (by intro d hd; cases hd)))
def cl_78416 : CNF.NClause := [(47,false),(77,false),(16,false),(75,false),(84,true)]
theorem der_78416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78416 :=
  CNF.rup_sound cl_78416 [cl_34362,cl_77297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34362 v h) (hints_cons _ _ _ (der_77297 v h) (by intro d hd; cases hd)))
def cl_78418 : CNF.NClause := [(47,false),(77,true),(84,false),(16,false),(89,false)]
theorem der_78418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78418 :=
  CNF.rup_sound cl_78418 [cl_52660,cl_77290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52660 v h) (hints_cons _ _ _ (der_77290 v h) (by intro d hd; cases hd)))
def cl_78419 : CNF.NClause := [(47,false),(77,false),(66,true),(84,true),(89,false)]
theorem der_78419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78419 :=
  CNF.rup_sound cl_78419 [cl_52662,cl_77297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52662 v h) (hints_cons _ _ _ (der_77297 v h) (by intro d hd; cases hd)))
def cl_78420 : CNF.NClause := [(47,false),(68,false),(84,true),(75,false),(89,false)]
theorem der_78420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78420 :=
  CNF.rup_sound cl_78420 [cl_34388,cl_77296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34388 v h) (hints_cons _ _ _ (der_77296 v h) (by intro d hd; cases hd)))
def cl_78421 : CNF.NClause := [(47,false),(66,true),(84,false),(68,false),(77,false)]
theorem der_78421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78421 :=
  CNF.rup_sound cl_78421 [cl_34393,cl_51801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34393 v h) (hints_cons _ _ _ (der_51801 v h) (by intro d hd; cases hd)))
def cl_78422 : CNF.NClause := [(47,false),(66,true),(75,false),(16,false),(68,false)]
theorem der_78422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78422 :=
  CNF.rup_sound cl_78422 [cl_34395,cl_51636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34395 v h) (hints_cons _ _ _ (der_51636 v h) (by intro d hd; cases hd)))
def cl_78424 : CNF.NClause := [(47,false),(77,false),(75,true),(89,true),(68,true)]
theorem der_78424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78424 :=
  CNF.rup_sound cl_78424 [cl_34402,cl_77281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34402 v h) (hints_cons _ _ _ (der_77281 v h) (by intro d hd; cases hd)))
def cl_78426 : CNF.NClause := [(21,false),(52,false),(67,false),(85,true),(73,false)]
theorem der_78426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78426 :=
  CNF.rup_sound cl_78426 [cl_34412,cl_77295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34412 v h) (hints_cons _ _ _ (der_77295 v h) (by intro d hd; cases hd)))
def cl_78427 : CNF.NClause := [(52,false),(67,false),(88,false),(73,false),(85,true)]
theorem der_78427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78427 :=
  CNF.rup_sound cl_78427 [cl_34430,cl_77298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34430 v h) (hints_cons _ _ _ (der_77298 v h) (by intro d hd; cases hd)))
def cl_78429 : CNF.NClause := [(66,true),(52,false),(21,true),(67,false),(85,false)]
theorem der_78429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78429 :=
  CNF.rup_sound cl_78429 [cl_52670,cl_77299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52670 v h) (hints_cons _ _ _ (der_77299 v h) (by intro d hd; cases hd)))
def cl_78430 : CNF.NClause := [(52,false),(67,true),(79,true),(85,false),(73,false)]
theorem der_78430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78430 :=
  CNF.rup_sound cl_78430 [cl_34441,cl_77295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34441 v h) (hints_cons _ _ _ (der_77295 v h) (by intro d hd; cases hd)))
def cl_78431 : CNF.NClause := [(66,true),(52,false),(79,false),(21,true),(67,false)]
theorem der_78431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78431 :=
  CNF.rup_sound cl_78431 [cl_52671,cl_77299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52671 v h) (hints_cons _ _ _ (der_77299 v h) (by intro d hd; cases hd)))
def cl_78432 : CNF.NClause := [(52,false),(66,true),(88,true),(73,true),(79,false)]
theorem der_78432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78432 :=
  CNF.rup_sound cl_78432 [cl_34446,cl_51858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34446 v h) (hints_cons _ _ _ (der_51858 v h) (by intro d hd; cases hd)))
def cl_78433 : CNF.NClause := [(52,false),(85,true),(73,false),(79,true),(67,false)]
theorem der_78433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78433 :=
  CNF.rup_sound cl_78433 [cl_34447,cl_78427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34447 v h) (hints_cons _ _ _ (der_78427 v h) (by intro d hd; cases hd)))
def cl_78435 : CNF.NClause := [(52,false),(79,true),(67,true),(85,true),(21,true)]
theorem der_78435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78435 :=
  CNF.rup_sound cl_78435 [cl_34450,cl_77030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34450 v h) (hints_cons _ _ _ (der_77030 v h) (by intro d hd; cases hd)))
def cl_78447 : CNF.NClause := [(44,false),(65,true),(78,false),(84,false),(88,false)]
theorem der_78447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78447 :=
  CNF.rup_sound cl_78447 [cl_52685,cl_77303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52685 v h) (hints_cons _ _ _ (der_77303 v h) (by intro d hd; cases hd)))
def cl_78449 : CNF.NClause := [(65,true),(88,false),(71,false),(44,false),(84,false)]
theorem der_78449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78449 :=
  CNF.rup_sound cl_78449 [cl_34504,cl_77315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34504 v h) (hints_cons _ _ _ (der_77315 v h) (by intro d hd; cases hd)))
def cl_78450 : CNF.NClause := [(44,false),(65,true),(78,true),(72,false),(88,false)]
theorem der_78450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78450 :=
  CNF.rup_sound cl_78450 [cl_34510,cl_77303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34510 v h) (hints_cons _ _ _ (der_77303 v h) (by intro d hd; cases hd)))
def cl_78451 : CNF.NClause := [(65,true),(77,true),(49,false),(73,true),(69,true)]
theorem der_78451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78451 :=
  CNF.rup_sound cl_78451 [cl_34560,cl_77333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34560 v h) (hints_cons _ _ _ (der_77333 v h) (by intro d hd; cases hd)))
def cl_78454 : CNF.NClause := [(49,false),(91,false),(73,true),(18,false),(86,false)]
theorem der_78454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78454 :=
  CNF.rup_sound cl_78454 [cl_52686,cl_77373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52686 v h) (hints_cons _ _ _ (der_77373 v h) (by intro d hd; cases hd)))
def cl_78455 : CNF.NClause := [(49,false),(86,true),(69,false),(18,false),(91,false)]
theorem der_78455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78455 :=
  CNF.rup_sound cl_78455 [cl_34569,cl_77328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34569 v h) (hints_cons _ _ _ (der_77328 v h) (by intro d hd; cases hd)))
def cl_78457 : CNF.NClause := [(52,false),(85,false),(73,true),(67,false),(79,false)]
theorem der_78457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78457 :=
  CNF.rup_sound cl_78457 [cl_52688,cl_52055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52688 v h) (hints_cons _ _ _ (der_52055 v h) (by intro d hd; cases hd)))
def cl_78459 : CNF.NClause := [(52,false),(73,true),(67,false),(79,false),(85,false)]
theorem der_78459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78459 :=
  CNF.rup_sound cl_78459 [cl_34576,cl_52055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34576 v h) (hints_cons _ _ _ (der_52055 v h) (by intro d hd; cases hd)))
def cl_78460 : CNF.NClause := [(21,false),(52,false),(66,false),(67,false),(85,true)]
theorem der_78460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78460 :=
  CNF.rup_sound cl_78460 [cl_34578,cl_77349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34578 v h) (hints_cons _ _ _ (der_77349 v h) (by intro d hd; cases hd)))
def cl_78461 : CNF.NClause := [(52,false),(85,true),(66,false),(88,true),(79,true)]
theorem der_78461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78461 :=
  CNF.rup_sound cl_78461 [cl_34587,cl_77349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34587 v h) (hints_cons _ _ _ (der_77349 v h) (by intro d hd; cases hd)))
def cl_78462 : CNF.NClause := [(45,false),(79,false),(89,true),(70,false),(63,false)]
theorem der_78462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78462 :=
  CNF.rup_sound cl_78462 [cl_52689,cl_51823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52689 v h) (hints_cons _ _ _ (der_51823 v h) (by intro d hd; cases hd)))
def cl_78463 : CNF.NClause := [(47,false),(77,false),(89,true),(16,false),(75,false)]
theorem der_78463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78463 :=
  CNF.rup_sound cl_78463 [cl_34596,cl_77297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34596 v h) (hints_cons _ _ _ (der_77297 v h) (by intro d hd; cases hd)))
def cl_78464 : CNF.NClause := [(44,false),(72,true),(88,false),(84,false),(13,false)]
theorem der_78464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78464 :=
  CNF.rup_sound cl_78464 [cl_34604,cl_77313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34604 v h) (hints_cons _ _ _ (der_77313 v h) (by intro d hd; cases hd)))
def cl_78465 : CNF.NClause := [(44,false),(78,true),(72,false),(88,false),(13,false)]
theorem der_78465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78465 :=
  CNF.rup_sound cl_78465 [cl_34606,cl_78450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34606 v h) (hints_cons _ _ _ (der_78450 v h) (by intro d hd; cases hd)))
def cl_78467 : CNF.NClause := [(44,false),(84,true),(78,true),(88,true),(72,false)]
theorem der_78467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78467 :=
  CNF.rup_sound cl_78467 [cl_34628,cl_77322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34628 v h) (hints_cons _ _ _ (der_77322 v h) (by intro d hd; cases hd)))
def cl_78468 : CNF.NClause := [(71,true),(13,true),(44,false),(84,true),(78,true)]
theorem der_78468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78468 :=
  CNF.rup_sound cl_78468 [cl_34629,cl_54393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34629 v h) (hints_cons _ _ _ (der_54393 v h) (by intro d hd; cases hd)))
def cl_78469 : CNF.NClause := [(44,false),(88,true),(72,false),(65,false),(71,false)]
theorem der_78469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78469 :=
  CNF.rup_sound cl_78469 [cl_52691,cl_77308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52691 v h) (hints_cons _ _ _ (der_77308 v h) (by intro d hd; cases hd)))
def cl_78470 : CNF.NClause := [(47,false),(66,true),(68,false),(89,false),(84,true)]
theorem der_78470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78470 :=
  CNF.rup_sound cl_78470 [cl_34637,cl_78420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34637 v h) (hints_cons _ _ _ (der_78420 v h) (by intro d hd; cases hd)))
def cl_78472 : CNF.NClause := [(86,true),(78,false),(64,false),(53,false),(67,false)]
theorem der_78472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78472 :=
  CNF.rup_sound cl_78472 [cl_34643,cl_51879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34643 v h) (hints_cons _ _ _ (der_51879 v h) (by intro d hd; cases hd)))
def cl_78474 : CNF.NClause := [(47,false),(75,true),(77,false),(84,false),(66,false)]
theorem der_78474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78474 :=
  CNF.rup_sound cl_78474 [cl_52693,cl_51817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52693 v h) (hints_cons _ _ _ (der_51817 v h) (by intro d hd; cases hd)))
def cl_78477 : CNF.NClause := [(45,false),(70,false),(86,true),(63,false),(79,false)]
theorem der_78477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78477 :=
  CNF.rup_sound cl_78477 [cl_52697,cl_78462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52697 v h) (hints_cons _ _ _ (der_78462 v h) (by intro d hd; cases hd)))
def cl_78478 : CNF.NClause := [(45,false),(63,false),(89,false),(79,true),(86,true)]
theorem der_78478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78478 :=
  CNF.rup_sound cl_78478 [cl_34670,cl_77448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34670 v h) (hints_cons _ _ _ (der_77448 v h) (by intro d hd; cases hd)))
def cl_78479 : CNF.NClause := [(45,false),(89,true),(63,false),(79,true),(86,false)]
theorem der_78479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78479 :=
  CNF.rup_sound cl_78479 [cl_34672,cl_77368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34672 v h) (hints_cons _ _ _ (der_77368 v h) (by intro d hd; cases hd)))
def cl_78480 : CNF.NClause := [(45,false),(70,false),(86,true),(14,false),(63,false)]
theorem der_78480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78480 :=
  CNF.rup_sound cl_78480 [cl_34674,cl_78477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34674 v h) (hints_cons _ _ _ (der_78477 v h) (by intro d hd; cases hd)))
def cl_78482 : CNF.NClause := [(44,false),(78,true),(88,false),(13,false),(71,false)]
theorem der_78482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78482 :=
  CNF.rup_sound cl_78482 [cl_52700,cl_77312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52700 v h) (hints_cons _ _ _ (der_77312 v h) (by intro d hd; cases hd)))
def cl_78483 : CNF.NClause := [(44,false),(78,true),(13,false),(84,false),(65,false)]
theorem der_78483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78483 :=
  CNF.rup_sound cl_78483 [cl_34680,cl_77359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34680 v h) (hints_cons _ _ _ (der_77359 v h) (by intro d hd; cases hd)))
def cl_78485 : CNF.NClause := [(49,false),(77,false),(69,true),(18,false),(91,false)]
theorem der_78485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78485 :=
  CNF.rup_sound cl_78485 [cl_52701,cl_51847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52701 v h) (hints_cons _ _ _ (der_51847 v h) (by intro d hd; cases hd)))
def cl_78487 : CNF.NClause := [(49,false),(91,true),(18,false),(65,false),(73,false)]
theorem der_78487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78487 :=
  CNF.rup_sound cl_78487 [cl_52702,cl_51843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52702 v h) (hints_cons _ _ _ (der_51843 v h) (by intro d hd; cases hd)))
def cl_78491 : CNF.NClause := [(52,false),(66,true),(79,false),(21,false),(85,false)]
theorem der_78491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78491 :=
  CNF.rup_sound cl_78491 [cl_34730,cl_51856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34730 v h) (hints_cons _ _ _ (der_51856 v h) (by intro d hd; cases hd)))
def cl_78493 : CNF.NClause := [(66,true),(52,false),(21,false),(85,false),(73,false)]
theorem der_78493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78493 :=
  CNF.rup_sound cl_78493 [cl_34737,cl_77295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34737 v h) (hints_cons _ _ _ (der_77295 v h) (by intro d hd; cases hd)))
def cl_78494 : CNF.NClause := [(66,true),(52,false),(21,false),(67,true),(73,false)]
theorem der_78494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78494 :=
  CNF.rup_sound cl_78494 [cl_34741,cl_77295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34741 v h) (hints_cons _ _ _ (der_77295 v h) (by intro d hd; cases hd)))
def cl_78496 : CNF.NClause := [(86,true),(64,false),(75,false),(22,false),(53,false)]
theorem der_78496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78496 :=
  CNF.rup_sound cl_78496 [cl_52706,cl_51862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52706 v h) (hints_cons _ _ _ (der_51862 v h) (by intro d hd; cases hd)))
def cl_78497 : CNF.NClause := [(75,true),(53,false),(64,false),(90,false),(22,false)]
theorem der_78497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78497 :=
  CNF.rup_sound cl_78497 [cl_34746,cl_77396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34746 v h) (hints_cons _ _ _ (der_77396 v h) (by intro d hd; cases hd)))
def cl_78499 : CNF.NClause := [(90,true),(53,false),(75,false),(64,false),(78,false)]
theorem der_78499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78499 :=
  CNF.rup_sound cl_78499 [cl_52707,cl_51879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52707 v h) (hints_cons _ _ _ (der_51879 v h) (by intro d hd; cases hd)))
def cl_78500 : CNF.NClause := [(78,true),(64,false),(86,false),(22,false),(53,false)]
theorem der_78500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78500 :=
  CNF.rup_sound cl_78500 [cl_34750,cl_51861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34750 v h) (hints_cons _ _ _ (der_51861 v h) (by intro d hd; cases hd)))
def cl_78503 : CNF.NClause := [(52,false),(67,true),(88,false),(85,false),(73,false)]
theorem der_78503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78503 :=
  CNF.rup_sound cl_78503 [cl_34756,cl_78430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34756 v h) (hints_cons _ _ _ (der_78430 v h) (by intro d hd; cases hd)))
def cl_78504 : CNF.NClause := [(52,false),(21,false),(73,true),(85,false),(88,false)]
theorem der_78504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78504 :=
  CNF.rup_sound cl_78504 [cl_34757,cl_77347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34757 v h) (hints_cons _ _ _ (der_77347 v h) (by intro d hd; cases hd)))
def cl_78505 : CNF.NClause := [(52,false),(67,true),(66,false),(85,false),(88,false)]
theorem der_78505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78505 :=
  CNF.rup_sound cl_78505 [cl_34759,cl_78503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34759 v h) (hints_cons _ _ _ (der_78503 v h) (by intro d hd; cases hd)))
def cl_78506 : CNF.NClause := [(21,false),(52,false),(85,true),(73,false),(88,false)]
theorem der_78506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78506 :=
  CNF.rup_sound cl_78506 [cl_34760,cl_77347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34760 v h) (hints_cons _ _ _ (der_77347 v h) (by intro d hd; cases hd)))
def cl_78508 : CNF.NClause := [(52,false),(67,true),(85,false),(66,false),(73,false)]
theorem der_78508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78508 :=
  CNF.rup_sound cl_78508 [cl_34764,cl_78430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34764 v h) (hints_cons _ _ _ (der_78430 v h) (by intro d hd; cases hd)))
def cl_78510 : CNF.NClause := [(21,false),(52,false),(85,true),(73,false),(66,false)]
theorem der_78510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78510 :=
  CNF.rup_sound cl_78510 [cl_34768,cl_77349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34768 v h) (hints_cons _ _ _ (der_77349 v h) (by intro d hd; cases hd)))
def cl_78511 : CNF.NClause := [(21,false),(52,false),(85,true),(88,true),(66,false)]
theorem der_78511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78511 :=
  CNF.rup_sound cl_78511 [cl_34769,cl_77349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34769 v h) (hints_cons _ _ _ (der_77349 v h) (by intro d hd; cases hd)))
def cl_78513 : CNF.NClause := [(75,true),(22,true),(90,false),(86,false),(53,false)]
theorem der_78513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78513 :=
  CNF.rup_sound cl_78513 [cl_52709,cl_77396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52709 v h) (hints_cons _ _ _ (der_77396 v h) (by intro d hd; cases hd)))
def cl_78515 : CNF.NClause := [(86,true),(64,true),(90,false),(53,false),(22,true)]
theorem der_78515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78515 :=
  CNF.rup_sound cl_78515 [cl_34773,cl_51876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34773 v h) (hints_cons _ _ _ (der_51876 v h) (by intro d hd; cases hd)))
def cl_78518 : CNF.NClause := [(90,true),(53,false),(22,true),(78,false),(75,false)]
theorem der_78518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78518 :=
  CNF.rup_sound cl_78518 [cl_34779,cl_78499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34779 v h) (hints_cons _ _ _ (der_78499 v h) (by intro d hd; cases hd)))
def cl_78521 : CNF.NClause := [(22,true),(53,false),(90,false),(75,false),(64,false)]
theorem der_78521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78521 :=
  CNF.rup_sound cl_78521 [cl_34783,cl_51875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34783 v h) (hints_cons _ _ _ (der_51875 v h) (by intro d hd; cases hd)))
def cl_78522 : CNF.NClause := [(75,true),(86,true),(64,false),(90,false),(53,false)]
theorem der_78522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78522 :=
  CNF.rup_sound cl_78522 [cl_34786,cl_77396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34786 v h) (hints_cons _ _ _ (der_77396 v h) (by intro d hd; cases hd)))
def cl_78523 : CNF.NClause := [(90,true),(75,true),(78,false),(53,false),(64,false)]
theorem der_78523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78523 :=
  CNF.rup_sound cl_78523 [cl_34790,cl_51879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34790 v h) (hints_cons _ _ _ (der_51879 v h) (by intro d hd; cases hd)))
def cl_78524 : CNF.NClause := [(72,true),(45,false),(89,false),(86,false),(79,false)]
theorem der_78524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78524 :=
  CNF.rup_sound cl_78524 [cl_52713,cl_51822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52713 v h) (hints_cons _ _ _ (der_51822 v h) (by intro d hd; cases hd)))
def cl_78525 : CNF.NClause := [(45,false),(72,false),(70,false),(89,false),(79,true)]
theorem der_78525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78525 :=
  CNF.rup_sound cl_78525 [cl_34799,cl_51887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34799 v h) (hints_cons _ _ _ (der_51887 v h) (by intro d hd; cases hd)))
def cl_78526 : CNF.NClause := [(72,true),(45,false),(89,false),(63,true),(86,false)]
theorem der_78526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78526 :=
  CNF.rup_sound cl_78526 [cl_52714,cl_51884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52714 v h) (hints_cons _ _ _ (der_51884 v h) (by intro d hd; cases hd)))
def cl_78527 : CNF.NClause := [(72,true),(45,false),(89,false),(63,true),(79,false)]
theorem der_78527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78527 :=
  CNF.rup_sound cl_78527 [cl_52715,cl_51889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52715 v h) (hints_cons _ _ _ (der_51889 v h) (by intro d hd; cases hd)))
def cl_78530 : CNF.NClause := [(45,false),(14,false),(86,false),(79,false),(89,true)]
theorem der_78530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78530 :=
  CNF.rup_sound cl_78530 [cl_34810,cl_77381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34810 v h) (hints_cons _ _ _ (der_77381 v h) (by intro d hd; cases hd)))
def cl_78532 : CNF.NClause := [(64,true),(86,false),(67,false),(53,false),(22,false)]
theorem der_78532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78532 :=
  CNF.rup_sound cl_78532 [cl_52717,cl_77397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52717 v h) (hints_cons _ _ _ (der_77397 v h) (by intro d hd; cases hd)))
def cl_78533 : CNF.NClause := [(75,true),(67,false),(53,false),(90,false),(86,false)]
theorem der_78533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78533 :=
  CNF.rup_sound cl_78533 [cl_34841,cl_77396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34841 v h) (hints_cons _ _ _ (der_77396 v h) (by intro d hd; cases hd)))
def cl_78535 : CNF.NClause := [(90,true),(75,true),(86,false),(53,false),(22,false)]
theorem der_78535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78535 :=
  CNF.rup_sound cl_78535 [cl_34862,cl_77397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34862 v h) (hints_cons _ _ _ (der_77397 v h) (by intro d hd; cases hd)))
def cl_78536 : CNF.NClause := [(90,true),(86,true),(53,false),(75,false),(78,false)]
theorem der_78536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78536 :=
  CNF.rup_sound cl_78536 [cl_34864,cl_78518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34864 v h) (hints_cons _ _ _ (der_78518 v h) (by intro d hd; cases hd)))
def cl_78542 : CNF.NClause := [(34,false),(75,true),(85,false),(65,false),(80,false)]
theorem der_78542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78542 :=
  CNF.rup_sound cl_78542 [cl_52720,cl_52400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52720 v h) (hints_cons _ _ _ (der_52400 v h) (by intro d hd; cases hd)))
def cl_78543 : CNF.NClause := [(54,false),(23,true),(81,false),(83,false),(65,false)]
theorem der_78543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78543 :=
  CNF.rup_sound cl_78543 [cl_52722,cl_77762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52722 v h) (hints_cons _ _ _ (der_77762 v h) (by intro d hd; cases hd)))
def cl_78544 : CNF.NClause := [(55,false),(76,true),(67,false),(63,false),(84,false)]
theorem der_78544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78544 :=
  CNF.rup_sound cl_78544 [cl_52723,cl_77885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52723 v h) (hints_cons _ _ _ (der_77885 v h) (by intro d hd; cases hd)))
def cl_78545 : CNF.NClause := [(49,false),(65,false),(73,false),(69,false),(18,true)]
theorem der_78545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78545 :=
  CNF.rup_sound cl_78545 [cl_52724,cl_78396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52724 v h) (hints_cons _ _ _ (der_78396 v h) (by intro d hd; cases hd)))
def cl_78546 : CNF.NClause := [(46,false),(15,true),(78,false),(79,false),(81,false)]
theorem der_78546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78546 :=
  CNF.rup_sound cl_78546 [cl_52725,cl_52039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52725 v h) (hints_cons _ _ _ (der_52039 v h) (by intro d hd; cases hd)))
def cl_78550 : CNF.NClause := [(113,true),(39,false),(38,true),(37,true),(36,false)]
theorem der_78550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78550 :=
  CNF.rup_sound cl_78550 [cl_37705,cl_64190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37705 v h) (hints_cons _ _ _ (der_64190 v h) (by intro d hd; cases hd)))
def cl_78551 : CNF.NClause := [(54,false),(23,true),(74,false),(83,false),(81,false)]
theorem der_78551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78551 :=
  CNF.rup_sound cl_78551 [cl_37408,cl_77740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37408 v h) (hints_cons _ _ _ (der_77740 v h) (by intro d hd; cases hd)))
def cl_78553 : CNF.NClause := [(34,false),(3,true),(70,false),(87,false),(65,false)]
theorem der_78553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78553 :=
  CNF.rup_sound cl_78553 [cl_52730,cl_50970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52730 v h) (hints_cons _ _ _ (der_50970 v h) (by intro d hd; cases hd)))
def cl_78554 : CNF.NClause := [(54,false),(65,true),(81,false),(74,false),(23,true)]
theorem der_78554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78554 :=
  CNF.rup_sound cl_78554 [cl_52731,cl_77066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52731 v h) (hints_cons _ _ _ (der_77066 v h) (by intro d hd; cases hd)))
def cl_78555 : CNF.NClause := [(903,false),(914,true),(921,true),(78,true),(6,true)]
theorem der_78555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78555 :=
  CNF.rup_sound cl_78555 [cl_39724,cl_15870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39724 v h) (hints_cons _ _ _ (der_15870 v h) (by intro d hd; cases hd)))
def cl_78562 : CNF.NClause := [(1072,false),(1060,true),(24,true),(26,true),(91,true)]
theorem der_78562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78562 :=
  CNF.rup_sound cl_78562 [cl_43594,cl_15930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43594 v h) (hints_cons _ _ _ (der_15930 v h) (by intro d hd; cases hd)))
def cl_78563 : CNF.NClause := [(82,true),(37,false),(6,true),(70,false),(74,false)]
theorem der_78563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78563 :=
  CNF.rup_sound cl_78563 [cl_52736,cl_77045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52736 v h) (hints_cons _ _ _ (der_77045 v h) (by intro d hd; cases hd)))
def cl_78571 : CNF.NClause := [(1077,false),(1071,true),(83,true),(4,true),(11,true)]
theorem der_78571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78571 :=
  CNF.rup_sound cl_78571 [cl_49128,cl_15929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49128 v h) (hints_cons _ _ _ (der_15929 v h) (by intro d hd; cases hd)))
def cl_78573 : CNF.NClause := [(246,false),(16,true),(4,true),(3,true),(68,true)]
theorem der_78573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78573 :=
  CNF.rup_sound cl_78573 [cl_54186,cl_13884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54186 v h) (hints_cons _ _ _ (inp_13884 v h) (by intro d hd; cases hd)))
def cl_78577 : CNF.NClause := [(1075,false),(1058,true),(28,true),(73,true),(1061,true)]
theorem der_78577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78577 :=
  CNF.rup_sound cl_78577 [cl_54416,cl_15927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54416 v h) (hints_cons _ _ _ (der_15927 v h) (by intro d hd; cases hd)))
def cl_78579 : CNF.NClause := [(54,false),(65,true),(67,false),(83,false),(89,false)]
theorem der_78579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78579 :=
  CNF.rup_sound cl_78579 [cl_54035,cl_77739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54035 v h) (hints_cons _ _ _ (der_77739 v h) (by intro d hd; cases hd)))
def cl_78580 : CNF.NClause := [(34,false),(85,true),(70,false),(65,false),(3,true)]
theorem der_78580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78580 :=
  CNF.rup_sound cl_78580 [cl_54150,cl_61268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54150 v h) (hints_cons _ _ _ (der_61268 v h) (by intro d hd; cases hd)))
def cl_78583 : CNF.NClause := [(42,false),(83,true),(69,false),(72,false),(80,false)]
theorem der_78583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78583 :=
  CNF.rup_sound cl_78583 [cl_58030,cl_50944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58030 v h) (hints_cons _ _ _ (der_50944 v h) (by intro d hd; cases hd)))
def cl_78584 : CNF.NClause := [(58,false),(85,true),(69,false),(78,false),(89,false)]
theorem der_78584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78584 :=
  CNF.rup_sound cl_78584 [cl_56428,cl_77696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56428 v h) (hints_cons _ _ _ (der_77696 v h) (by intro d hd; cases hd)))
def cl_78585 : CNF.NClause := [(138,false),(45,true),(89,false),(63,false),(129,true)]
theorem der_78585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78585 :=
  CNF.rup_sound cl_78585 [cl_57608,cl_62563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57608 v h) (hints_cons _ _ _ (der_62563 v h) (by intro d hd; cases hd)))
def cl_78587 : CNF.NClause := [(42,false),(66,false),(90,false),(11,true),(72,false)]
theorem der_78587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78587 :=
  CNF.rup_sound cl_78587 [cl_59410,cl_77969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59410 v h) (hints_cons _ _ _ (der_77969 v h) (by intro d hd; cases hd)))
def cl_78588 : CNF.NClause := [(125,false),(71,true),(137,true),(131,true),(150,true)]
theorem der_78588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78588 :=
  CNF.rup_sound cl_78588 [cl_58792,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58792 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_78589 : CNF.NClause := [(59,false),(81,false),(73,false),(28,true),(62,false)]
theorem der_78589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78589 :=
  CNF.rup_sound cl_78589 [cl_58253,cl_78180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58253 v h) (hints_cons _ _ _ (der_78180 v h) (by intro d hd; cases hd)))
def cl_78590 : CNF.NClause := [(55,false),(91,false),(67,false),(84,true),(63,false)]
theorem der_78590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78590 :=
  CNF.rup_sound cl_78590 [cl_59312,cl_50875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59312 v h) (hints_cons _ _ _ (der_50875 v h) (by intro d hd; cases hd)))
def cl_78591 : CNF.NClause := [(55,false),(91,true),(84,false),(76,false),(67,false)]
theorem der_78591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78591 :=
  CNF.rup_sound cl_78591 [cl_59415,cl_77893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59415 v h) (hints_cons _ _ _ (der_77893 v h) (by intro d hd; cases hd)))
def cl_78592 : CNF.NClause := [(130,false),(37,true),(12,false),(74,false),(78,false)]
theorem der_78592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78592 :=
  CNF.rup_sound cl_78592 [cl_59592,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59592 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_78593 : CNF.NClause := [(75,true),(908,false),(9,false),(921,true),(26,true)]
theorem der_78593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78593 :=
  CNF.rup_sound cl_78593 [cl_56463,cl_49811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56463 v h) (hints_cons _ _ _ (der_49811 v h) (by intro d hd; cases hd)))
def cl_78595 : CNF.NClause := [(85,true),(136,false),(129,true),(145,true),(3,true)]
theorem der_78595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78595 :=
  CNF.rup_sound cl_78595 [cl_56071,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56071 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_78596 : CNF.NClause := [(85,true),(127,false),(21,true),(129,true),(151,true)]
theorem der_78596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78596 :=
  CNF.rup_sound cl_78596 [cl_56433,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56433 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_78597 : CNF.NClause := [(696,false),(686,true),(63,true),(706,true),(18,true)]
theorem der_78597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78597 :=
  CNF.rup_sound cl_78597 [cl_56618,cl_14320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56618 v h) (hints_cons _ _ _ (inp_14320 v h) (by intro d hd; cases hd)))
def cl_78598 : CNF.NClause := [(135,false),(69,true),(20,true),(144,true),(142,true)]
theorem der_78598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78598 :=
  CNF.rup_sound cl_78598 [cl_61397,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61397 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_78601 : CNF.NClause := [(132,false),(39,true),(79,false),(11,false),(76,false)]
theorem der_78601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78601 :=
  CNF.rup_sound cl_78601 [cl_61773,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61773 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_78603 : CNF.NClause := [(39,true),(28,false),(132,false),(76,false),(79,false)]
theorem der_78603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78603 :=
  CNF.rup_sound cl_78603 [cl_61653,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61653 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_78604 : CNF.NClause := [(34,false),(3,true),(85,false),(65,false),(75,false)]
theorem der_78604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78604 :=
  CNF.rup_sound cl_78604 [cl_63622,cl_52382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63622 v h) (hints_cons _ _ _ (der_52382 v h) (by intro d hd; cases hd)))
def cl_78606 : CNF.NClause := [(151,false),(58,true),(76,false),(85,false),(89,false)]
theorem der_78606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78606 :=
  CNF.rup_sound cl_78606 [cl_63068,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63068 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_78608 : CNF.NClause := [(32,false),(87,true),(66,false),(81,true),(76,false)]
theorem der_78608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78608 :=
  CNF.rup_sound cl_78608 [cl_61778,cl_34151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61778 v h) (hints_cons _ _ _ (der_34151 v h) (by intro d hd; cases hd)))
def cl_78610 : CNF.NClause := [(42,false),(90,false),(72,false),(11,true),(80,false)]
theorem der_78610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78610 :=
  CNF.rup_sound cl_78610 [cl_60209,cl_77947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60209 v h) (hints_cons _ _ _ (der_77947 v h) (by intro d hd; cases hd)))
def cl_78612 : CNF.NClause := [(301,false),(75,true),(282,true),(10,true),(5,true)]
theorem der_78612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78612 :=
  CNF.rup_sound cl_78612 [cl_61365,cl_13937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61365 v h) (hints_cons _ _ _ (inp_13937 v h) (by intro d hd; cases hd)))
def cl_78613 : CNF.NClause := [(42,false),(11,true),(80,false),(69,false),(66,false)]
theorem der_78613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78613 :=
  CNF.rup_sound cl_78613 [cl_61904,cl_58640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61904 v h) (hints_cons _ _ _ (der_58640 v h) (by intro d hd; cases hd)))
def cl_78617 : CNF.NClause := [(38,false),(80,false),(89,true),(73,false),(64,false)]
theorem der_78617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78617 :=
  CNF.rup_sound cl_78617 [cl_61500,cl_78148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61500 v h) (hints_cons _ _ _ (der_78148 v h) (by intro d hd; cases hd)))
def cl_78619 : CNF.NClause := [(914,false),(902,true),(80,true),(7,true),(928,true)]
theorem der_78619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78619 :=
  CNF.rup_sound cl_78619 [cl_61260,cl_15881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61260 v h) (hints_cons _ _ _ (der_15881 v h) (by intro d hd; cases hd)))
def cl_78620 : CNF.NClause := [(47,true),(140,false),(77,false),(27,false),(150,true)]
theorem der_78620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78620 :=
  CNF.rup_sound cl_78620 [cl_66469,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66469 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_78621 : CNF.NClause := [(130,false),(37,true),(74,false),(18,false),(78,false)]
theorem der_78621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78621 :=
  CNF.rup_sound cl_78621 [cl_65588,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65588 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_78622 : CNF.NClause := [(44,true),(137,false),(88,false),(84,false),(78,false)]
theorem der_78622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78622 :=
  CNF.rup_sound cl_78622 [cl_67688,cl_76536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67688 v h) (hints_cons _ _ _ (der_76536 v h) (by intro d hd; cases hd)))
def cl_78624 : CNF.NClause := [(62,false),(153,false),(88,false),(74,false),(60,true)]
theorem der_78624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78624 :=
  CNF.rup_sound cl_78624 [cl_66131,cl_57227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66131 v h) (hints_cons _ _ _ (der_57227 v h) (by intro d hd; cases hd)))
def cl_78626 : CNF.NClause := [(928,false),(901,true),(909,true),(74,true),(918,true)]
theorem der_78626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78626 :=
  CNF.rup_sound cl_78626 [cl_72590,cl_76288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72590 v h) (hints_cons _ _ _ (der_76288 v h) (by intro d hd; cases hd)))
def cl_78627 : CNF.NClause := [(9,false),(69,true),(81,true),(28,true),(11,true)]
theorem der_78627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78627 :=
  CNF.rup_sound cl_78627 [cl_72057,cl_76877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72057 v h) (hints_cons _ _ _ (der_76877 v h) (by intro d hd; cases hd)))
def cl_78629 : CNF.NClause := [(17,false),(40,true),(133,false),(81,false),(88,false)]
theorem der_78629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78629 :=
  CNF.rup_sound cl_78629 [cl_72987,cl_60497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72987 v h) (hints_cons _ _ _ (der_60497 v h) (by intro d hd; cases hd)))
def cl_78631 : CNF.NClause := [(52,false),(79,false),(85,false),(88,true),(67,false)]
theorem der_78631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78631 :=
  CNF.rup_sound cl_78631 [cl_73361,cl_78459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73361 v h) (hints_cons _ _ _ (der_78459 v h) (by intro d hd; cases hd)))
def cl_78632 : CNF.NClause := [(16,false),(12,true),(68,true),(84,true),(28,true)]
theorem der_78632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78632 :=
  CNF.rup_sound cl_78632 [cl_73348,cl_76637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73348 v h) (hints_cons _ _ _ (der_76637 v h) (by intro d hd; cases hd)))
def cl_78633 : CNF.NClause := [(43,true),(136,false),(24,false),(85,false),(64,false)]
theorem der_78633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78633 :=
  CNF.rup_sound cl_78633 [cl_75884,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75884 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_78634 : CNF.NClause := [(42,false),(83,true),(69,false),(80,false),(90,true)]
theorem der_78634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78634 :=
  CNF.rup_sound cl_78634 [cl_76220,cl_50944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76220 v h) (hints_cons _ _ _ (der_50944 v h) (by intro d hd; cases hd)))
def cl_78635 : CNF.NClause := [(2,true),(26,true),(15,true),(79,false),(21,true),(14,true)]
theorem der_78635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78635 :=
  CNF.rup_sound cl_78635 [cl_1150,cl_53786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1150 v h) (hints_cons _ _ _ (der_53786 v h) (by intro d hd; cases hd)))
def cl_78636 : CNF.NClause := [(21,true),(15,true),(2,true),(8,true),(79,false),(26,true)]
theorem der_78636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78636 :=
  CNF.rup_sound cl_78636 [cl_1148,cl_53786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1148 v h) (hints_cons _ _ _ (der_53786 v h) (by intro d hd; cases hd)))
def cl_78637 : CNF.NClause := [(21,true),(14,true),(2,true),(8,true),(79,false),(26,true)]
theorem der_78637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78637 :=
  CNF.rup_sound cl_78637 [cl_1144,cl_53786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1144 v h) (hints_cons _ _ _ (der_53786 v h) (by intro d hd; cases hd)))
def cl_78639 : CNF.NClause := [(21,true),(15,true),(8,true),(14,true),(2,true),(79,false)]
theorem der_78639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78639 :=
  CNF.rup_sound cl_78639 [cl_1120,cl_78636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1120 v h) (hints_cons _ _ _ (der_78636 v h) (by intro d hd; cases hd)))
def cl_78640 : CNF.NClause := [(21,true),(15,true),(26,true),(8,true),(79,false),(14,true)]
theorem der_78640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78640 :=
  CNF.rup_sound cl_78640 [cl_1151,cl_78636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1151 v h) (hints_cons _ _ _ (der_78636 v h) (by intro d hd; cases hd)))
def cl_78641 : CNF.NClause := [(39,false),(65,true),(8,true),(82,false),(79,true),(90,true)]
theorem der_78641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78641 :=
  CNF.rup_sound cl_78641 [cl_26453,cl_77601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26453 v h) (hints_cons _ _ _ (der_77601 v h) (by intro d hd; cases hd)))
def cl_78642 : CNF.NClause := [(39,false),(76,false),(8,true),(79,true),(90,true),(68,true)]
theorem der_78642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78642 :=
  CNF.rup_sound cl_78642 [cl_26477,cl_77033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26477 v h) (hints_cons _ _ _ (der_77033 v h) (by intro d hd; cases hd)))
def cl_78643 : CNF.NClause := [(60,false),(29,true),(68,false),(88,false),(86,false),(62,false)]
theorem der_78643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78643 :=
  CNF.rup_sound cl_78643 [cl_34912,cl_61896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34912 v h) (hints_cons _ _ _ (der_61896 v h) (by intro d hd; cases hd)))
def cl_78644 : CNF.NClause := [(60,false),(80,true),(88,true),(74,true),(86,true),(68,false)]
theorem der_78644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78644 :=
  CNF.rup_sound cl_78644 [cl_27277,cl_77860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27277 v h) (hints_cons _ _ _ (der_77860 v h) (by intro d hd; cases hd)))
def cl_78645 : CNF.NClause := [(42,false),(72,true),(90,true),(11,true),(83,true),(69,false)]
theorem der_78645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78645 :=
  CNF.rup_sound cl_78645 [cl_27634,cl_78634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27634 v h) (hints_cons _ _ _ (der_78634 v h) (by intro d hd; cases hd)))
def cl_78646 : CNF.NClause := [(72,true),(43,false),(91,true),(64,true),(81,true),(85,true)]
theorem der_78646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78646 :=
  CNF.rup_sound cl_78646 [cl_27987,cl_62741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27987 v h) (hints_cons _ _ _ (der_62741 v h) (by intro d hd; cases hd)))
def cl_78647 : CNF.NClause := [(38,false),(89,true),(73,true),(64,true),(71,false),(80,false)]
theorem der_78647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78647 :=
  CNF.rup_sound cl_78647 [cl_28206,cl_77133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28206 v h) (hints_cons _ _ _ (der_77133 v h) (by intro d hd; cases hd)))
def cl_78648 : CNF.NClause := [(59,false),(62,false),(81,false),(90,true),(84,false),(28,false)]
theorem der_78648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78648 :=
  CNF.rup_sound cl_78648 [cl_34950,cl_78181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34950 v h) (hints_cons _ _ _ (der_78181 v h) (by intro d hd; cases hd)))
def cl_78649 : CNF.NClause := [(57,false),(91,true),(62,false),(83,false),(26,false),(79,false)]
theorem der_78649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78649 :=
  CNF.rup_sound cl_78649 [cl_34954,cl_52576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34954 v h) (hints_cons _ _ _ (der_52576 v h) (by intro d hd; cases hd)))
def cl_78650 : CNF.NClause := [(151,false),(58,true),(76,false),(85,false),(89,false),(78,false)]
theorem der_78650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78650 :=
  CNF.rup_sound cl_78650 [cl_38351,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38351 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_78651 : CNF.NClause := [(90,false),(146,false),(53,true),(86,false),(75,false),(64,false)]
theorem der_78651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78651 :=
  CNF.rup_sound cl_78651 [cl_75856,cl_15788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75856 v h) (hints_cons _ _ _ (der_15788 v h) (by intro d hd; cases hd)))
def cl_78652 : CNF.NClause := [(35,true),(87,false),(78,false),(63,false),(128,false),(83,false)]
theorem der_78652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78652 :=
  CNF.rup_sound cl_78652 [cl_54056,cl_62171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54056 v h) (hints_cons _ _ _ (der_62171 v h) (by intro d hd; cases hd)))
def cl_78653 : CNF.NClause := [(46,false),(92,false),(80,false),(79,true),(81,false),(78,false)]
theorem der_78653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78653 :=
  CNF.rup_sound cl_78653 [cl_53794,cl_77911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53794 v h) (hints_cons _ _ _ (der_77911 v h) (by intro d hd; cases hd)))
def cl_78655 : CNF.NClause := [(34,false),(75,true),(87,false),(70,false),(3,false),(65,false)]
theorem der_78655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78655 :=
  CNF.rup_sound cl_78655 [cl_54166,cl_50970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54166 v h) (hints_cons _ _ _ (der_50970 v h) (by intro d hd; cases hd)))
def cl_78656 : CNF.NClause := [(39,true),(28,false),(68,false),(76,false),(79,false),(132,false)]
theorem der_78656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78656 :=
  CNF.rup_sound cl_78656 [cl_58471,cl_60459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58471 v h) (hints_cons _ _ _ (der_60459 v h) (by intro d hd; cases hd)))
def cl_78657 : CNF.NClause := [(39,true),(132,false),(65,false),(79,false),(76,false),(90,false)]
theorem der_78657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78657 :=
  CNF.rup_sound cl_78657 [cl_57439,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57439 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_78659 : CNF.NClause := [(47,true),(140,false),(75,false),(89,false),(84,false),(141,true)]
theorem der_78659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78659 :=
  CNF.rup_sound cl_78659 [cl_57778,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57778 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_78660 : CNF.NClause := [(47,true),(15,false),(75,false),(84,false),(89,false),(140,false)]
theorem der_78660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78660 :=
  CNF.rup_sound cl_78660 [cl_56455,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56455 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_78661 : CNF.NClause := [(77,false),(140,false),(89,false),(84,false),(47,true),(150,true)]
theorem der_78661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78661 :=
  CNF.rup_sound cl_78661 [cl_57618,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57618 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_78663 : CNF.NClause := [(130,false),(37,true),(12,false),(78,false),(74,false),(70,false)]
theorem der_78663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78663 :=
  CNF.rup_sound cl_78663 [cl_59393,cl_57205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59393 v h) (hints_cons _ _ _ (der_57205 v h) (by intro d hd; cases hd)))
def cl_78664 : CNF.NClause := [(21,false),(4,true),(3,true),(85,true),(73,true),(7,true)]
theorem der_78664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78664 :=
  CNF.rup_sound cl_78664 [cl_56150,cl_60483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56150 v h) (hints_cons _ _ _ (der_60483 v h) (by intro d hd; cases hd)))
def cl_78665 : CNF.NClause := [(33,true),(5,false),(1,false),(29,false),(126,false),(79,false)]
theorem der_78665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78665 :=
  CNF.rup_sound cl_78665 [cl_61673,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61673 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_78666 : CNF.NClause := [(33,true),(29,false),(5,false),(69,false),(3,false),(126,false)]
theorem der_78666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78666 :=
  CNF.rup_sound cl_78666 [cl_61709,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61709 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_78667 : CNF.NClause := [(87,false),(33,true),(69,false),(5,false),(126,false),(29,false)]
theorem der_78667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78667 :=
  CNF.rup_sound cl_78667 [cl_61649,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61649 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_78668 : CNF.NClause := [(35,true),(3,false),(128,false),(83,false),(63,false),(73,false)]
theorem der_78668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78668 :=
  CNF.rup_sound cl_78668 [cl_62665,cl_62286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62665 v h) (hints_cons _ _ _ (der_62286 v h) (by intro d hd; cases hd)))
def cl_78669 : CNF.NClause := [(49,false),(73,false),(91,false),(69,true),(18,false),(86,false)]
theorem der_78669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78669 :=
  CNF.rup_sound cl_78669 [cl_63604,cl_51681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63604 v h) (hints_cons _ _ _ (der_51681 v h) (by intro d hd; cases hd)))
def cl_78670 : CNF.NClause := [(59,true),(73,false),(84,false),(90,false),(152,false),(70,false)]
theorem der_78670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78670 :=
  CNF.rup_sound cl_78670 [cl_61573,cl_75861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61573 v h) (hints_cons _ _ _ (der_75861 v h) (by intro d hd; cases hd)))
def cl_78671 : CNF.NClause := [(46,true),(92,false),(139,false),(79,false),(81,false),(78,false)]
theorem der_78671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78671 :=
  CNF.rup_sound cl_78671 [cl_60480,cl_62452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60480 v h) (hints_cons _ _ _ (der_62452 v h) (by intro d hd; cases hd)))
def cl_78672 : CNF.NClause := [(87,false),(33,true),(126,false),(69,false),(74,false),(5,false)]
theorem der_78672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78672 :=
  CNF.rup_sound cl_78672 [cl_61600,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61600 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_78673 : CNF.NClause := [(150,false),(57,true),(18,false),(62,false),(17,true),(5,false)]
theorem der_78673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78673 :=
  CNF.rup_sound cl_78673 [cl_61661,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61661 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_78675 : CNF.NClause := [(144,false),(51,true),(14,true),(92,false),(67,false),(68,false)]
theorem der_78675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78675 :=
  CNF.rup_sound cl_78675 [cl_60445,cl_62569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60445 v h) (hints_cons _ _ _ (der_62569 v h) (by intro d hd; cases hd)))
def cl_78676 : CNF.NClause := [(17,false),(40,true),(82,false),(81,false),(69,false),(133,false)]
theorem der_78676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78676 :=
  CNF.rup_sound cl_78676 [cl_62333,cl_60497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62333 v h) (hints_cons _ _ _ (der_60497 v h) (by intro d hd; cases hd)))
def cl_78677 : CNF.NClause := [(38,true),(73,false),(89,false),(71,false),(64,false),(131,false)]
theorem der_78677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78677 :=
  CNF.rup_sound cl_78677 [cl_62670,cl_72318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62670 v h) (hints_cons _ _ _ (der_72318 v h) (by intro d hd; cases hd)))
def cl_78678 : CNF.NClause := [(49,true),(12,false),(69,false),(77,false),(142,false),(73,false)]
theorem der_78678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78678 :=
  CNF.rup_sound cl_78678 [cl_62684,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62684 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_78679 : CNF.NClause := [(19,false),(146,false),(64,false),(53,true),(75,false),(86,false)]
theorem der_78679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78679 :=
  CNF.rup_sound cl_78679 [cl_63479,cl_76538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63479 v h) (hints_cons _ _ _ (der_76538 v h) (by intro d hd; cases hd)))
def cl_78681 : CNF.NClause := [(756,false),(771,true),(3,true),(5,true),(20,true),(85,true)]
theorem der_78681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78681 :=
  CNF.rup_sound cl_78681 [cl_60983,cl_14378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60983 v h) (hints_cons _ _ _ (inp_14378 v h) (by intro d hd; cases hd)))
def cl_78686 : CNF.NClause := [(130,false),(37,true),(66,false),(74,false),(18,false),(78,false)]
theorem der_78686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78686 :=
  CNF.rup_sound cl_78686 [cl_64072,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64072 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_78687 : CNF.NClause := [(32,true),(125,false),(71,false),(3,false),(76,false),(86,false)]
theorem der_78687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78687 :=
  CNF.rup_sound cl_78687 [cl_69086,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69086 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_78688 : CNF.NClause := [(76,true),(133,true),(131,true),(144,true),(130,true),(139,true)]
theorem der_78688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78688 :=
  CNF.rup_sound cl_78688 [cl_68821,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68821 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_78689 : CNF.NClause := [(151,false),(58,true),(76,false),(85,false),(16,false),(78,false)]
theorem der_78689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78689 :=
  CNF.rup_sound cl_78689 [cl_68783,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68783 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_78690 : CNF.NClause := [(43,true),(136,false),(131,true),(141,true),(24,false),(68,false)]
theorem der_78690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78690 :=
  CNF.rup_sound cl_78690 [cl_68681,cl_62572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68681 v h) (hints_cons _ _ _ (der_62572 v h) (by intro d hd; cases hd)))
def cl_78691 : CNF.NClause := [(52,true),(145,false),(29,false),(73,false),(135,true),(67,false)]
theorem der_78691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78691 :=
  CNF.rup_sound cl_78691 [cl_68880,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68880 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_78692 : CNF.NClause := [(52,true),(145,false),(73,false),(88,false),(135,true),(67,false)]
theorem der_78692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78692 :=
  CNF.rup_sound cl_78692 [cl_65820,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65820 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_78693 : CNF.NClause := [(41,true),(5,false),(134,false),(76,false),(73,false),(75,false)]
theorem der_78693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78693 :=
  CNF.rup_sound cl_78693 [cl_69439,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69439 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_78695 : CNF.NClause := [(143,false),(50,true),(85,false),(15,true),(18,false),(90,false)]
theorem der_78695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78695 :=
  CNF.rup_sound cl_78695 [cl_66609,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66609 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_78696 : CNF.NClause := [(35,true),(2,false),(128,false),(63,false),(83,false),(73,false)]
theorem der_78696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78696 :=
  CNF.rup_sound cl_78696 [cl_69090,cl_62286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69090 v h) (hints_cons _ _ _ (der_62286 v h) (by intro d hd; cases hd)))
def cl_78697 : CNF.NClause := [(32,true),(125,false),(71,false),(4,false),(76,false),(86,false)]
theorem der_78697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78697 :=
  CNF.rup_sound cl_78697 [cl_69694,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69694 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_78698 : CNF.NClause := [(20,false),(36,true),(129,false),(84,false),(83,false),(86,false)]
theorem der_78698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78698 :=
  CNF.rup_sound cl_78698 [cl_65753,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65753 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_78699 : CNF.NClause := [(1060,false),(37,true),(91,false),(82,false),(74,false),(78,false)]
theorem der_78699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78699 :=
  CNF.rup_sound cl_78699 [cl_73292,cl_54836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73292 v h) (hints_cons _ _ _ (der_54836 v h) (by intro d hd; cases hd)))
def cl_78700 : CNF.NClause := [(9,false),(23,true),(14,true),(63,true),(81,true),(19,true)]
theorem der_78700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78700 :=
  CNF.rup_sound cl_78700 [cl_72027,cl_76988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72027 v h) (hints_cons _ _ _ (der_76988 v h) (by intro d hd; cases hd)))
def cl_78701 : CNF.NClause := [(47,true),(77,false),(140,false),(89,false),(84,false),(75,false)]
theorem der_78701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78701 :=
  CNF.rup_sound cl_78701 [cl_72201,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72201 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_78702 : CNF.NClause := [(4,false),(33,true),(5,false),(69,false),(74,false),(126,false)]
theorem der_78702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78702 :=
  CNF.rup_sound cl_78702 [cl_73819,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73819 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_78703 : CNF.NClause := [(138,false),(45,true),(89,false),(70,false),(63,false),(86,false)]
theorem der_78703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78703 :=
  CNF.rup_sound cl_78703 [cl_74168,cl_56745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74168 v h) (hints_cons _ _ _ (der_56745 v h) (by intro d hd; cases hd)))
def cl_78705 : CNF.NClause := [(37,true),(130,false),(74,false),(24,false),(9,false),(78,false)]
theorem der_78705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78705 :=
  CNF.rup_sound cl_78705 [cl_71571,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71571 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_78706 : CNF.NClause := [(37,true),(130,false),(91,false),(74,false),(70,false),(78,false)]
theorem der_78706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78706 :=
  CNF.rup_sound cl_78706 [cl_75225,cl_57205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75225 v h) (hints_cons _ _ _ (der_57205 v h) (by intro d hd; cases hd)))
def cl_78709 : CNF.NClause := [(151,false),(58,true),(76,false),(85,false),(7,true),(14,false),(78,false)]
theorem der_78709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78709 :=
  CNF.rup_sound cl_78709 [cl_42018,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42018 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_78715 : CNF.NClause := [(17,false),(9,true),(86,false),(80,false),(60,true),(68,false),(153,false)]
theorem der_78715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78715 :=
  CNF.rup_sound cl_78715 [cl_53755,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53755 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_78719 : CNF.NClause := [(58,true),(151,false),(141,true),(78,false),(89,false),(148,true),(85,false)]
theorem der_78719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78719 :=
  CNF.rup_sound cl_78719 [cl_56937,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56937 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_78720 : CNF.NClause := [(151,false),(58,true),(4,true),(76,false),(85,false),(128,true),(89,false)]
theorem der_78720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78720 :=
  CNF.rup_sound cl_78720 [cl_58542,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58542 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_78722 : CNF.NClause := [(33,true),(1,false),(69,false),(126,false),(131,true),(74,false),(84,false)]
theorem der_78722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78722 :=
  CNF.rup_sound cl_78722 [cl_58713,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58713 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_78724 : CNF.NClause := [(17,true),(144,false),(67,false),(68,false),(51,true),(92,false),(71,false)]
theorem der_78724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78724 :=
  CNF.rup_sound cl_78724 [cl_57422,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57422 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_78725 : CNF.NClause := [(34,true),(1,false),(127,false),(80,false),(5,true),(16,false),(65,false)]
theorem der_78725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78725 :=
  CNF.rup_sound cl_78725 [cl_59483,cl_62580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59483 v h) (hints_cons _ _ _ (der_62580 v h) (by intro d hd; cases hd)))
def cl_78726 : CNF.NClause := [(33,true),(126,false),(74,false),(69,false),(131,true),(3,false),(79,false)]
theorem der_78726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78726 :=
  CNF.rup_sound cl_78726 [cl_59419,cl_62575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59419 v h) (hints_cons _ _ _ (der_62575 v h) (by intro d hd; cases hd)))
def cl_78728 : CNF.NClause := [(5,true),(49,true),(73,false),(69,false),(142,false),(77,false),(6,false)]
theorem der_78728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78728 :=
  CNF.rup_sound cl_78728 [cl_56570,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56570 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_78729 : CNF.NClause := [(33,true),(87,false),(126,false),(69,false),(131,true),(74,false),(79,false)]
theorem der_78729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78729 :=
  CNF.rup_sound cl_78729 [cl_59184,cl_62575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59184 v h) (hints_cons _ _ _ (der_62575 v h) (by intro d hd; cases hd)))
def cl_78731 : CNF.NClause := [(138,true),(139,true),(151,true),(142,true),(141,true),(131,true),(74,true)]
theorem der_78731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78731 :=
  CNF.rup_sound cl_78731 [cl_63532,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63532 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_78733 : CNF.NClause := [(52,true),(145,false),(88,false),(128,true),(7,true),(135,true),(67,false)]
theorem der_78733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78733 :=
  CNF.rup_sound cl_78733 [cl_63928,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63928 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_78734 : CNF.NClause := [(4,false),(33,true),(126,false),(131,true),(79,false),(69,false),(74,false)]
theorem der_78734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78734 :=
  CNF.rup_sound cl_78734 [cl_63359,cl_62575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63359 v h) (hints_cons _ _ _ (der_62575 v h) (by intro d hd; cases hd)))
def cl_78735 : CNF.NClause := [(33,true),(126,false),(69,false),(3,false),(131,true),(74,false),(15,false)]
theorem der_78735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78735 :=
  CNF.rup_sound cl_78735 [cl_63039,cl_62575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63039 v h) (hints_cons _ _ _ (der_62575 v h) (by intro d hd; cases hd)))
def cl_78736 : CNF.NClause := [(33,true),(1,false),(126,false),(84,false),(6,false),(131,true),(79,false)]
theorem der_78736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78736 :=
  CNF.rup_sound cl_78736 [cl_61664,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61664 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_78739 : CNF.NClause := [(47,true),(140,false),(3,true),(84,false),(150,true),(141,true),(89,false)]
theorem der_78739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78739 :=
  CNF.rup_sound cl_78739 [cl_61780,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61780 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_78740 : CNF.NClause := [(17,false),(52,true),(73,false),(145,false),(85,false),(135,true),(67,false)]
theorem der_78740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78740 :=
  CNF.rup_sound cl_78740 [cl_66405,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66405 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_78741 : CNF.NClause := [(7,true),(91,false),(55,true),(76,false),(11,true),(148,false),(67,false)]
theorem der_78741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78741 :=
  CNF.rup_sound cl_78741 [cl_68823,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68823 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_78742 : CNF.NClause := [(129,true),(40,true),(133,false),(21,false),(81,false),(131,true),(75,false)]
theorem der_78742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78742 :=
  CNF.rup_sound cl_78742 [cl_69584,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69584 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_78743 : CNF.NClause := [(129,true),(40,true),(81,false),(13,false),(133,false),(131,true),(75,false)]
theorem der_78743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78743 :=
  CNF.rup_sound cl_78743 [cl_69572,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69572 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_78744 : CNF.NClause := [(43,true),(6,false),(141,true),(136,false),(68,false),(85,false),(131,true)]
theorem der_78744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78744 :=
  CNF.rup_sound cl_78744 [cl_69465,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69465 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_78745 : CNF.NClause := [(77,false),(47,true),(140,false),(14,false),(84,false),(150,true),(7,true)]
theorem der_78745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78745 :=
  CNF.rup_sound cl_78745 [cl_66372,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66372 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_78746 : CNF.NClause := [(57,true),(91,false),(150,false),(83,false),(79,false),(71,false),(152,true)]
theorem der_78746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78746 :=
  CNF.rup_sound cl_78746 [cl_72890,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72890 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_78747 : CNF.NClause := [(60,true),(153,false),(88,false),(80,false),(74,false),(152,true),(68,false)]
theorem der_78747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78747 :=
  CNF.rup_sound cl_78747 [cl_73562,cl_57227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73562 v h) (hints_cons _ _ _ (der_57227 v h) (by intro d hd; cases hd)))
def cl_78749 : CNF.NClause := [(55,true),(26,false),(80,false),(148,false),(84,false),(67,false),(18,true)]
theorem der_78749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78749 :=
  CNF.rup_sound cl_78749 [cl_71432,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71432 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_78751 : CNF.NClause := [(6,false),(80,false),(24,false),(84,false),(55,true),(67,false),(76,false),(63,false)]
theorem der_78751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78751 :=
  CNF.rup_sound cl_78751 [cl_35646,cl_60999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35646 v h) (hints_cons _ _ _ (der_60999 v h) (by intro d hd; cases hd)))
def cl_78752 : CNF.NClause := [(907,false),(67,true),(10,true),(17,true),(27,true),(1,true),(23,true),(22,true)]
theorem der_78752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78752 :=
  CNF.rup_sound cl_78752 [cl_36603,cl_77433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36603 v h) (hints_cons _ _ _ (der_77433 v h) (by intro d hd; cases hd)))
def cl_78753 : CNF.NClause := [(23,true),(145,true),(90,false),(78,false),(64,false),(146,false),(86,false),(53,true)]
theorem der_78753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78753 :=
  CNF.rup_sound cl_78753 [cl_38130,cl_62576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38130 v h) (hints_cons _ _ _ (der_62576 v h) (by intro d hd; cases hd)))
def cl_78756 : CNF.NClause := [(1056,true),(1063,true),(1,false),(71,true),(1078,true),(1057,true),(7,true),(1068,true)]
theorem der_78756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78756 :=
  CNF.rup_sound cl_78756 [cl_52794,cl_76889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52794 v h) (hints_cons _ _ _ (der_76889 v h) (by intro d hd; cases hd)))
def cl_78758 : CNF.NClause := [(915,true),(916,true),(903,true),(914,true),(913,true),(91,true),(908,true),(24,false)]
theorem der_78758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78758 :=
  CNF.rup_sound cl_78758 [cl_52797,cl_76578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52797 v h) (hints_cons _ _ _ (der_76578 v h) (by intro d hd; cases hd)))
def cl_78760 : CNF.NClause := [(1080,false),(83,false),(75,false),(62,false),(57,true),(71,false),(79,false),(27,false)]
theorem der_78760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78760 :=
  CNF.rup_sound cl_78760 [cl_74769,cl_15931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74769 v h) (hints_cons _ _ _ (der_15931 v h) (by intro d hd; cases hd)))
def cl_78762 : CNF.NClause := [(92,false),(138,true),(135,true),(134,false),(75,false),(74,false),(41,true),(73,false)]
theorem der_78762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78762 :=
  CNF.rup_sound cl_78762 [cl_43711,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43711 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_78763 : CNF.NClause := [(92,false),(138,true),(41,true),(134,false),(73,false),(74,false),(75,false),(76,false)]
theorem der_78763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78763 :=
  CNF.rup_sound cl_78763 [cl_45009,cl_15776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45009 v h) (hints_cons _ _ _ (der_15776 v h) (by intro d hd; cases hd)))
def cl_78765 : CNF.NClause := [(50,true),(143,false),(139,true),(142,true),(90,false),(85,false),(63,false),(71,false)]
theorem der_78765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78765 :=
  CNF.rup_sound cl_78765 [cl_41656,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41656 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_78766 : CNF.NClause := [(7,false),(73,false),(71,false),(89,false),(5,false),(64,false),(38,true),(80,false)]
theorem der_78766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78766 :=
  CNF.rup_sound cl_78766 [cl_43145,cl_53703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43145 v h) (hints_cons _ _ _ (der_53703 v h) (by intro d hd; cases hd)))
def cl_78767 : CNF.NClause := [(12,true),(57,true),(75,false),(150,false),(79,false),(6,false),(152,true),(83,false)]
theorem der_78767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78767 :=
  CNF.rup_sound cl_78767 [cl_41082,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41082 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_78768 : CNF.NClause := [(8,false),(7,false),(38,true),(64,false),(73,false),(71,false),(89,false),(80,false)]
theorem der_78768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78768 :=
  CNF.rup_sound cl_78768 [cl_44024,cl_53703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44024 v h) (hints_cons _ _ _ (der_53703 v h) (by intro d hd; cases hd)))
def cl_78769 : CNF.NClause := [(9,false),(68,false),(76,false),(8,false),(65,false),(28,false),(39,true),(79,false)]
theorem der_78769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78769 :=
  CNF.rup_sound cl_78769 [cl_52812,cl_57760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52812 v h) (hints_cons _ _ _ (der_57760 v h) (by intro d hd; cases hd)))
def cl_78771 : CNF.NClause := [(36,true),(92,false),(83,false),(86,false),(24,false),(5,false),(3,false),(82,false)]
theorem der_78771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78771 :=
  CNF.rup_sound cl_78771 [cl_52819,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52819 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_78772 : CNF.NClause := [(36,true),(92,false),(82,false),(5,false),(3,false),(86,false),(13,false),(83,false)]
theorem der_78772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78772 :=
  CNF.rup_sound cl_78772 [cl_52820,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52820 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_78774 : CNF.NClause := [(5,false),(36,true),(92,false),(16,false),(3,false),(82,false),(86,false),(83,false)]
theorem der_78774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78774 :=
  CNF.rup_sound cl_78774 [cl_52829,cl_52764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52829 v h) (hints_cons _ _ _ (der_52764 v h) (by intro d hd; cases hd)))
def cl_78775 : CNF.NClause := [(1059,false),(92,false),(3,false),(36,true),(83,false),(82,false),(86,false),(28,true)]
theorem der_78775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78775 :=
  CNF.rup_sound cl_78775 [cl_52830,cl_15911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52830 v h) (hints_cons _ _ _ (der_15911 v h) (by intro d hd; cases hd)))
def cl_78776 : CNF.NClause := [(21,false),(52,true),(88,false),(73,false),(1,false),(85,false),(79,false),(67,false)]
theorem der_78776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78776 :=
  CNF.rup_sound cl_78776 [cl_48306,cl_56510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48306 v h) (hints_cons _ _ _ (der_56510 v h) (by intro d hd; cases hd)))
def cl_78779 : CNF.NClause := [(46,false),(32,false),(51,false),(54,false),(36,false),(60,false),(33,true),(58,false)]
theorem der_78779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78779 :=
  CNF.rup_sound cl_78779 [cl_64327,cl_64264] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64327 v h) (hints_cons _ _ _ (der_64264 v h) (by intro d hd; cases hd)))
def cl_78780 : CNF.NClause := [(39,true),(8,false),(76,false),(82,false),(79,false),(68,false),(22,false),(65,false)]
theorem der_78780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78780 :=
  CNF.rup_sound cl_78780 [cl_47782,cl_56836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47782 v h) (hints_cons _ _ _ (der_56836 v h) (by intro d hd; cases hd)))
def cl_78781 : CNF.NClause := [(46,false),(58,false),(96,false),(36,false),(33,true),(51,false),(54,false),(60,false)]
theorem der_78781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78781 :=
  CNF.rup_sound cl_78781 [cl_64337,cl_64264] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64337 v h) (hints_cons _ _ _ (der_64264 v h) (by intro d hd; cases hd)))
def cl_78782 : CNF.NClause := [(143,false),(50,true),(17,true),(71,false),(3,true),(63,false),(18,false),(90,false)]
theorem der_78782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78782 :=
  CNF.rup_sound cl_78782 [cl_54652,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54652 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_78785 : CNF.NClause := [(19,false),(90,false),(74,false),(18,false),(63,false),(85,false),(71,false),(50,true)]
theorem der_78785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78785 :=
  CNF.rup_sound cl_78785 [cl_54330,cl_41733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54330 v h) (hints_cons _ _ _ (der_41733 v h) (by intro d hd; cases hd)))
def cl_78788 : CNF.NClause := [(20,true),(926,true),(918,true),(68,true),(921,true),(910,true),(16,false),(925,true)]
theorem der_78788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78788 :=
  CNF.rup_sound cl_78788 [cl_48882,cl_76857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48882 v h) (hints_cons _ _ _ (der_76857 v h) (by intro d hd; cases hd)))
def cl_78789 : CNF.NClause := [(153,false),(60,true),(150,true),(68,false),(88,false),(74,false),(80,false),(151,true)]
theorem der_78789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78789 :=
  CNF.rup_sound cl_78789 [cl_56674,cl_57227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56674 v h) (hints_cons _ _ _ (der_57227 v h) (by intro d hd; cases hd)))
def cl_78790 : CNF.NClause := [(137,false),(44,true),(88,false),(84,false),(65,false),(78,false),(135,true),(134,true)]
theorem der_78790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78790 :=
  CNF.rup_sound cl_78790 [cl_58303,cl_66628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58303 v h) (hints_cons _ _ _ (der_66628 v h) (by intro d hd; cases hd)))
def cl_78792 : CNF.NClause := [(75,true),(131,true),(137,true),(130,true),(150,true),(147,true),(142,false),(129,true)]
theorem der_78792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78792 :=
  CNF.rup_sound cl_78792 [cl_58689,cl_62576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58689 v h) (hints_cons _ _ _ (der_62576 v h) (by intro d hd; cases hd)))
def cl_78796 : CNF.NClause := [(47,true),(9,false),(16,false),(89,false),(18,false),(84,false),(66,false),(68,false)]
theorem der_78796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78796 :=
  CNF.rup_sound cl_78796 [cl_58120,cl_41231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58120 v h) (hints_cons _ _ _ (der_41231 v h) (by intro d hd; cases hd)))
def cl_78797 : CNF.NClause := [(43,true),(6,false),(141,true),(85,false),(136,false),(68,false),(81,false),(131,true)]
theorem der_78797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78797 :=
  CNF.rup_sound cl_78797 [cl_57739,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57739 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_78799 : CNF.NClause := [(129,true),(40,true),(150,true),(63,false),(81,false),(88,false),(133,false),(131,true)]
theorem der_78799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78799 :=
  CNF.rup_sound cl_78799 [cl_58538,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58538 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_78800 : CNF.NClause := [(129,true),(40,true),(63,false),(133,false),(88,false),(81,false),(69,false),(131,true)]
theorem der_78800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78800 :=
  CNF.rup_sound cl_78800 [cl_57738,cl_60497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57738 v h) (hints_cons _ _ _ (der_60497 v h) (by intro d hd; cases hd)))
def cl_78802 : CNF.NClause := [(7,true),(6,false),(55,true),(128,true),(76,false),(67,false),(148,false),(11,true)]
theorem der_78802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78802 :=
  CNF.rup_sound cl_78802 [cl_59088,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59088 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_78803 : CNF.NClause := [(150,true),(136,true),(131,true),(129,true),(69,true),(132,true),(135,true),(148,true)]
theorem der_78803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78803 :=
  CNF.rup_sound cl_78803 [cl_56884,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56884 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_78804 : CNF.NClause := [(129,true),(134,true),(131,true),(17,true),(153,true),(148,true),(70,true),(135,true)]
theorem der_78804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78804 :=
  CNF.rup_sound cl_78804 [cl_58289,cl_69297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58289 v h) (hints_cons _ _ _ (der_69297 v h) (by intro d hd; cases hd)))
def cl_78806 : CNF.NClause := [(28,false),(26,true),(53,true),(131,true),(78,false),(141,true),(86,false),(146,false)]
theorem der_78806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78806 :=
  CNF.rup_sound cl_78806 [cl_59737,cl_63071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59737 v h) (hints_cons _ _ _ (der_63071 v h) (by intro d hd; cases hd)))
def cl_78807 : CNF.NClause := [(50,true),(28,false),(85,false),(63,false),(141,true),(143,false),(74,false),(142,true)]
theorem der_78807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78807 :=
  CNF.rup_sound cl_78807 [cl_58239,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58239 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_78809 : CNF.NClause := [(17,false),(54,true),(11,true),(142,true),(81,false),(147,false),(74,false),(89,false)]
theorem der_78809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78809 :=
  CNF.rup_sound cl_78809 [cl_63419,cl_63040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63419 v h) (hints_cons _ _ _ (der_63040 v h) (by intro d hd; cases hd)))
def cl_78813 : CNF.NClause := [(57,true),(62,false),(150,false),(138,true),(83,false),(126,true),(71,false),(91,false)]
theorem der_78813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78813 :=
  CNF.rup_sound cl_78813 [cl_63793,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63793 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_78814 : CNF.NClause := [(49,false),(111,true),(32,false),(34,false),(94,false),(50,false),(121,false),(105,false)]
theorem der_78814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78814 :=
  CNF.rup_sound cl_78814 [cl_62914,cl_76708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62914 v h) (hints_cons _ _ _ (der_76708 v h) (by intro d hd; cases hd)))
def cl_78815 : CNF.NClause := [(49,true),(26,true),(69,false),(142,false),(73,false),(17,true),(86,false),(12,false)]
theorem der_78815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78815 :=
  CNF.rup_sound cl_78815 [cl_59920,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59920 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_78816 : CNF.NClause := [(246,false),(60,true),(80,false),(3,true),(88,false),(68,false),(74,false),(86,false)]
theorem der_78816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78816 :=
  CNF.rup_sound cl_78816 [cl_64006,cl_13884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64006 v h) (hints_cons _ _ _ (inp_13884 v h) (by intro d hd; cases hd)))
def cl_78820 : CNF.NClause := [(151,false),(75,true),(135,true),(143,true),(126,true),(139,true),(144,true),(141,true)]
theorem der_78820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78820 :=
  CNF.rup_sound cl_78820 [cl_61698,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61698 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_78822 : CNF.NClause := [(20,false),(138,true),(134,false),(41,true),(76,false),(73,false),(135,true),(75,false)]
theorem der_78822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78822 :=
  CNF.rup_sound cl_78822 [cl_69076,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69076 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_78824 : CNF.NClause := [(91,false),(57,true),(79,false),(150,false),(141,true),(152,true),(71,false),(11,true)]
theorem der_78824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78824 :=
  CNF.rup_sound cl_78824 [cl_69256,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69256 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_78826 : CNF.NClause := [(905,false),(928,true),(912,true),(904,true),(79,true),(916,true),(14,false),(906,true)]
theorem der_78826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78826 :=
  CNF.rup_sound cl_78826 [cl_68462,cl_49770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68462 v h) (hints_cons _ _ _ (der_49770 v h) (by intro d hd; cases hd)))
def cl_78827 : CNF.NClause := [(54,true),(14,false),(65,false),(81,false),(141,true),(147,false),(74,false),(11,true)]
theorem der_78827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78827 :=
  CNF.rup_sound cl_78827 [cl_68978,cl_63040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68978 v h) (hints_cons _ _ _ (der_63040 v h) (by intro d hd; cases hd)))
def cl_78828 : CNF.NClause := [(68,true),(150,true),(148,true),(129,true),(145,true),(141,true),(135,true),(146,false)]
theorem der_78828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78828 :=
  CNF.rup_sound cl_78828 [cl_68008,cl_61595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68008 v h) (hints_cons _ _ _ (der_61595 v h) (by intro d hd; cases hd)))
def cl_78829 : CNF.NClause := [(79,true),(139,true),(127,true),(137,true),(144,true),(142,true),(148,true),(146,false)]
theorem der_78829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78829 :=
  CNF.rup_sound cl_78829 [cl_69665,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69665 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_78830 : CNF.NClause := [(138,true),(144,true),(76,true),(127,true),(143,true),(128,true),(135,true),(142,true)]
theorem der_78830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78830 :=
  CNF.rup_sound cl_78830 [cl_73021,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73021 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_78831 : CNF.NClause := [(134,true),(84,true),(131,true),(153,true),(147,true),(132,true),(143,true),(133,false)]
theorem der_78831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78831 :=
  CNF.rup_sound cl_78831 [cl_70219,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70219 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_78833 : CNF.NClause := [(153,true),(133,false),(79,true),(127,true),(131,true),(143,true),(128,true),(135,true)]
theorem der_78833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78833 :=
  CNF.rup_sound cl_78833 [cl_71463,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71463 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_78834 : CNF.NClause := [(57,true),(150,false),(79,false),(24,false),(71,false),(152,true),(83,false),(18,true)]
theorem der_78834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78834 :=
  CNF.rup_sound cl_78834 [cl_73919,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73919 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_78836 : CNF.NClause := [(145,true),(148,true),(132,true),(137,true),(70,true),(141,true),(146,false),(142,true)]
theorem der_78836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78836 :=
  CNF.rup_sound cl_78836 [cl_70035,cl_69297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70035 v h) (hints_cons _ _ _ (der_69297 v h) (by intro d hd; cases hd)))
def cl_78838 : CNF.NClause := [(80,true),(136,true),(130,true),(151,true),(131,true),(152,true),(135,true),(142,true)]
theorem der_78838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78838 :=
  CNF.rup_sound cl_78838 [cl_71224,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71224 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_78839 : CNF.NClause := [(55,true),(26,false),(76,false),(63,false),(84,false),(24,false),(80,false),(67,false)]
theorem der_78839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78839 :=
  CNF.rup_sound cl_78839 [cl_69995,cl_61877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69995 v h) (hints_cons _ _ _ (der_61877 v h) (by intro d hd; cases hd)))
def cl_78841 : CNF.NClause := [(6,true),(145,true),(80,false),(55,true),(22,true),(148,false),(63,false),(18,false),(76,false)]
theorem der_78841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78841 :=
  CNF.rup_sound cl_78841 [cl_38010,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38010 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_78847 : CNF.NClause := [(6,true),(55,true),(63,false),(22,false),(18,false),(24,false),(76,false),(84,false),(80,false)]
theorem der_78847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78847 :=
  CNF.rup_sound cl_78847 [cl_38013,cl_57925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38013 v h) (hints_cons _ _ _ (der_57925 v h) (by intro d hd; cases hd)))
def cl_78848 : CNF.NClause := [(20,false),(69,false),(67,false),(68,false),(92,false),(6,true),(71,false),(51,true),(14,false)]
theorem der_78848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78848 :=
  CNF.rup_sound cl_78848 [cl_37968,cl_60622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37968 v h) (hints_cons _ _ _ (der_60622 v h) (by intro d hd; cases hd)))
def cl_78849 : CNF.NClause := [(6,true),(55,true),(76,false),(63,false),(21,false),(24,false),(80,false),(18,false),(84,false)]
theorem der_78849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78849 :=
  CNF.rup_sound cl_78849 [cl_52858,cl_57925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52858 v h) (hints_cons _ _ _ (der_57925 v h) (by intro d hd; cases hd)))
def cl_78850 : CNF.NClause := [(89,true),(145,true),(137,true),(139,true),(23,false),(128,false),(146,true),(135,true),(125,true)]
theorem der_78850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78850 :=
  CNF.rup_sound cl_78850 [cl_52859,cl_49761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52859 v h) (hints_cons _ _ _ (der_49761 v h) (by intro d hd; cases hd)))
def cl_78861 : CNF.NClause := [(587,false),(585,true),(68,false),(9,false),(60,true),(80,false),(14,true),(74,false),(86,false)]
theorem der_78861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78861 :=
  CNF.rup_sound cl_78861 [cl_52879,cl_14214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52879 v h) (hints_cons _ _ _ (inp_14214 v h) (by intro d hd; cases hd)))
def cl_78862 : CNF.NClause := [(55,true),(91,false),(24,false),(80,false),(76,false),(22,true),(147,true),(63,false),(148,false)]
theorem der_78862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78862 :=
  CNF.rup_sound cl_78862 [cl_52880,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52880 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_78864 : CNF.NClause := [(48,false),(46,false),(98,false),(118,false),(120,false),(34,false),(116,false),(54,false),(106,false)]
theorem der_78864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78864 :=
  CNF.rup_sound cl_78864 [cl_42829,cl_55085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42829 v h) (hints_cons _ _ _ (der_55085 v h) (by intro d hd; cases hd)))
def cl_78868 : CNF.NClause := [(66,true),(6,false),(141,true),(131,true),(137,true),(135,true),(153,true),(129,true),(132,true)]
theorem der_78868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78868 :=
  CNF.rup_sound cl_78868 [cl_46916,cl_56933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46916 v h) (hints_cons _ _ _ (der_56933 v h) (by intro d hd; cases hd)))
def cl_78873 : CNF.NClause := [(9,true),(52,true),(135,true),(73,false),(17,false),(85,false),(145,false),(67,false),(79,false)]
theorem der_78873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78873 :=
  CNF.rup_sound cl_78873 [cl_52898,cl_15787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52898 v h) (hints_cons _ _ _ (der_15787 v h) (by intro d hd; cases hd)))
def cl_78874 : CNF.NClause := [(39,true),(76,false),(22,false),(8,false),(11,true),(65,false),(7,false),(68,false),(79,false)]
theorem der_78874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78874 :=
  CNF.rup_sound cl_78874 [cl_49516,cl_57760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49516 v h) (hints_cons _ _ _ (der_57760 v h) (by intro d hd; cases hd)))
def cl_78881 : CNF.NClause := [(17,true),(76,true),(133,true),(145,true),(135,true),(151,true),(140,false),(131,true),(129,true)]
theorem der_78881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78881 :=
  CNF.rup_sound cl_78881 [cl_57526,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57526 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_78883 : CNF.NClause := [(153,false),(60,true),(150,true),(80,false),(152,true),(68,false),(13,false),(74,false),(9,true)]
theorem der_78883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78883 :=
  CNF.rup_sound cl_78883 [cl_57549,cl_57227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57549 v h) (hints_cons _ _ _ (der_57227 v h) (by intro d hd; cases hd)))
def cl_78884 : CNF.NClause := [(137,false),(4,true),(84,false),(128,true),(135,true),(134,true),(65,false),(44,true),(88,false)]
theorem der_78884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78884 :=
  CNF.rup_sound cl_78884 [cl_58759,cl_66628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58759 v h) (hints_cons _ _ _ (der_66628 v h) (by intro d hd; cases hd)))
def cl_78887 : CNF.NClause := [(70,true),(132,false),(131,true),(144,true),(141,true),(128,true),(148,true),(143,true),(129,true)]
theorem der_78887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78887 :=
  CNF.rup_sound cl_78887 [cl_56876,cl_69297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56876 v h) (hints_cons _ _ _ (der_69297 v h) (by intro d hd; cases hd)))
def cl_78888 : CNF.NClause := [(7,true),(145,false),(21,false),(66,false),(79,false),(67,false),(88,false),(85,false),(73,true)]
theorem der_78888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78888 :=
  CNF.rup_sound cl_78888 [cl_56613,cl_49967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56613 v h) (hints_cons _ _ _ (der_49967 v h) (by intro d hd; cases hd)))
def cl_78890 : CNF.NClause := [(17,true),(43,true),(85,false),(91,false),(126,false),(81,false),(68,false),(22,true),(7,true)]
theorem der_78890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78890 :=
  CNF.rup_sound cl_78890 [cl_58717,cl_15788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58717 v h) (hints_cons _ _ _ (der_15788 v h) (by intro d hd; cases hd)))
def cl_78892 : CNF.NClause := [(59,false),(93,false),(121,false),(52,false),(119,false),(47,false),(46,false),(116,false),(98,false)]
theorem der_78892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78892 :=
  CNF.rup_sound cl_78892 [cl_57352,cl_58527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57352 v h) (hints_cons _ _ _ (der_58527 v h) (by intro d hd; cases hd)))
def cl_78897 : CNF.NClause := [(17,true),(129,true),(131,true),(135,true),(147,true),(76,true),(138,true),(145,true),(133,true)]
theorem der_78897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78897 :=
  CNF.rup_sound cl_78897 [cl_57129,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57129 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_78899 : CNF.NClause := [(144,true),(150,true),(135,true),(125,true),(132,true),(141,true),(78,true),(147,true),(148,true)]
theorem der_78899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78899 :=
  CNF.rup_sound cl_78899 [cl_62307,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62307 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_78901 : CNF.NClause := [(43,true),(136,false),(140,true),(91,false),(132,true),(144,true),(64,false),(85,false),(72,false)]
theorem der_78901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78901 :=
  CNF.rup_sound cl_78901 [cl_62339,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62339 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_78903 : CNF.NClause := [(126,true),(139,true),(153,true),(135,true),(147,true),(150,true),(144,true),(142,false),(81,true)]
theorem der_78903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78903 :=
  CNF.rup_sound cl_78903 [cl_62353,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62353 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_78904 : CNF.NClause := [(142,false),(29,false),(136,true),(128,true),(88,true),(138,true),(152,true),(135,true),(131,true)]
theorem der_78904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78904 :=
  CNF.rup_sound cl_78904 [cl_68778,cl_76553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68778 v h) (hints_cons _ _ _ (der_76553 v h) (by intro d hd; cases hd)))
def cl_78905 : CNF.NClause := [(140,true),(129,true),(131,true),(133,false),(127,true),(137,true),(139,true),(74,true),(141,true)]
theorem der_78905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78905 :=
  CNF.rup_sound cl_78905 [cl_67994,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67994 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_78906 : CNF.NClause := [(59,false),(48,false),(100,false),(105,false),(33,false),(108,false),(114,false),(39,false),(118,false)]
theorem der_78906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78906 :=
  CNF.rup_sound cl_78906 [cl_66487,cl_55076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66487 v h) (hints_cons _ _ _ (der_55076 v h) (by intro d hd; cases hd)))
def cl_78908 : CNF.NClause := [(63,true),(139,false),(127,true),(136,false),(88,true),(143,true),(131,true),(134,true),(135,true)]
theorem der_78908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78908 :=
  CNF.rup_sound cl_78908 [cl_71094,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71094 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_78909 : CNF.NClause := [(133,true),(74,true),(132,true),(141,true),(151,false),(135,true),(152,true),(131,true),(128,true)]
theorem der_78909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78909 :=
  CNF.rup_sound cl_78909 [cl_70475,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70475 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_78913 : CNF.NClause := [(133,true),(125,true),(145,true),(151,false),(127,true),(143,true),(131,true),(68,true),(135,true)]
theorem der_78913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78913 :=
  CNF.rup_sound cl_78913 [cl_70924,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70924 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_78914 : CNF.NClause := [(1064,true),(1074,true),(1061,true),(1066,true),(84,true),(1076,true),(28,true),(1073,true),(1072,true)]
theorem der_78914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78914 :=
  CNF.rup_sound cl_78914 [cl_74759,cl_76864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74759 v h) (hints_cons _ _ _ (der_76864 v h) (by intro d hd; cases hd)))
def cl_78915 : CNF.NClause := [(133,false),(151,true),(141,true),(74,true),(132,true),(131,true),(152,true),(135,true),(128,true)]
theorem der_78915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78915 :=
  CNF.rup_sound cl_78915 [cl_70831,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70831 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_78918 : CNF.NClause := [(150,true),(140,true),(138,false),(125,true),(141,true),(74,true),(132,true),(135,true),(142,true)]
theorem der_78918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78918 :=
  CNF.rup_sound cl_78918 [cl_75206,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75206 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_78925 : CNF.NClause := [(914,true),(905,true),(918,true),(901,true),(88,true),(919,true),(900,true),(926,true),(9,false),(917,true)]
theorem der_78925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78925 :=
  CNF.rup_sound cl_78925 [cl_37724,cl_76539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37724 v h) (hints_cons _ _ _ (der_76539 v h) (by intro d hd; cases hd)))
def cl_78927 : CNF.NClause := [(1069,true),(1060,true),(1071,true),(1075,true),(1066,true),(7,true),(1065,true),(1,false),(1078,true),(71,true)]
theorem der_78927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78927 :=
  CNF.rup_sound cl_78927 [cl_38890,cl_77242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38890 v h) (hints_cons _ _ _ (der_77242 v h) (by intro d hd; cases hd)))
def cl_78929 : CNF.NClause := [(52,true),(23,true),(66,false),(145,false),(17,true),(9,true),(22,true),(73,false),(13,false),(85,false)]
theorem der_78929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78929 :=
  CNF.rup_sound cl_78929 [cl_38982,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38982 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_78944 : CNF.NClause := [(36,true),(148,true),(22,false),(85,false),(83,false),(92,false),(3,false),(28,true),(126,true),(129,false)]
theorem der_78944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78944 :=
  CNF.rup_sound cl_78944 [cl_47995,cl_62455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47995 v h) (hints_cons _ _ _ (der_62455 v h) (by intro d hd; cases hd)))
def cl_78952 : CNF.NClause := [(55,true),(5,true),(4,false),(148,false),(13,true),(6,false),(152,true),(126,true),(67,false),(80,false)]
theorem der_78952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78952 :=
  CNF.rup_sound cl_78952 [cl_48132,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48132 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_78955 : CNF.NClause := [(52,false),(97,false),(39,false),(58,false),(116,false),(113,false),(53,false),(96,false),(99,false),(119,false)]
theorem der_78955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78955 :=
  CNF.rup_sound cl_78955 [cl_64381,cl_54743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64381 v h) (hints_cons _ _ _ (der_54743 v h) (by intro d hd; cases hd)))
def cl_78956 : CNF.NClause := [(75,true),(152,true),(128,true),(148,true),(126,true),(136,true),(129,true),(134,true),(143,false),(135,true)]
theorem der_78956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78956 :=
  CNF.rup_sound cl_78956 [cl_58277,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58277 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_78957 : CNF.NClause := [(43,true),(12,false),(68,false),(81,false),(10,false),(85,false),(6,false),(131,true),(141,true),(136,false)]
theorem der_78957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78957 :=
  CNF.rup_sound cl_78957 [cl_56726,cl_49832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56726 v h) (hints_cons _ _ _ (der_49832 v h) (by intro d hd; cases hd)))
def cl_78958 : CNF.NClause := [(38,true),(60,false),(58,false),(116,false),(115,false),(98,false),(122,false),(45,false),(55,false),(109,false)]
theorem der_78958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78958 :=
  CNF.rup_sound cl_78958 [cl_58179,cl_64296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58179 v h) (hints_cons _ _ _ (der_64296 v h) (by intro d hd; cases hd)))
def cl_78965 : CNF.NClause := [(50,false),(35,false),(114,false),(104,false),(60,false),(101,false),(96,false),(109,false),(42,true),(34,false)]
theorem der_78965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78965 :=
  CNF.rup_sound cl_78965 [cl_62986,cl_76672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62986 v h) (hints_cons _ _ _ (der_76672 v h) (by intro d hd; cases hd)))
def cl_78967 : CNF.NClause := [(50,false),(55,false),(60,false),(48,false),(58,true),(122,false),(99,false),(57,false),(95,false),(53,false)]
theorem der_78967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78967 :=
  CNF.rup_sound cl_78967 [cl_63850,cl_76973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63850 v h) (hints_cons _ _ _ (der_76973 v h) (by intro d hd; cases hd)))
def cl_78968 : CNF.NClause := [(1066,false),(43,true),(12,false),(1072,true),(72,false),(85,false),(2,false),(64,false),(1060,true),(81,false)]
theorem der_78968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78968 :=
  CNF.rup_sound cl_78968 [cl_60935,cl_66240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60935 v h) (hints_cons _ _ _ (der_66240 v h) (by intro d hd; cases hd)))
def cl_78972 : CNF.NClause := [(133,true),(153,true),(141,true),(151,true),(150,true),(85,true),(132,true),(128,true),(135,true),(142,true)]
theorem der_78972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78972 :=
  CNF.rup_sound cl_78972 [cl_71369,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71369 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_78980 : CNF.NClause := [(42,false),(37,false),(33,false),(46,true),(35,false),(110,false),(101,false),(118,false),(95,false),(43,false),(113,false)]
theorem der_78980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78980 :=
  CNF.rup_sound cl_78980 [cl_52974,cl_76765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52974 v h) (hints_cons _ _ _ (der_76765 v h) (by intro d hd; cases hd)))
def cl_78993 : CNF.NClause := [(1059,true),(1056,true),(6,false),(1078,true),(1075,true),(1073,true),(1069,true),(1071,true),(1076,true),(70,true),(1083,true)]
theorem der_78993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78993 :=
  CNF.rup_sound cl_78993 [cl_52991,cl_49809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52991 v h) (hints_cons _ _ _ (der_49809 v h) (by intro d hd; cases hd)))
def cl_79017 : CNF.NClause := [(39,false),(44,false),(105,false),(43,false),(37,false),(101,false),(119,false),(47,true),(42,true),(102,false),(97,false)]
theorem der_79017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79017 :=
  CNF.rup_sound cl_79017 [cl_64351,cl_69034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64351 v h) (hints_cons _ _ _ (der_69034 v h) (by intro d hd; cases hd)))
def cl_79028 : CNF.NClause := [(121,false),(42,true),(65,false),(53,true),(79,false),(59,true),(76,false),(86,false),(146,false),(78,false),(75,false)]
theorem der_79028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79028 :=
  CNF.rup_sound cl_79028 [cl_64752,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64752 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_79033 : CNF.NClause := [(35,true),(99,false),(51,false),(55,false),(106,false),(123,false),(44,false),(40,false),(54,true),(113,false),(101,false)]
theorem der_79033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79033 :=
  CNF.rup_sound cl_79033 [cl_68078,cl_49962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68078 v h) (hints_cons _ _ _ (der_49962 v h) (by intro d hd; cases hd)))
def cl_79041 : CNF.NClause := [(133,true),(140,false),(147,true),(85,true),(151,true),(125,true),(142,true),(131,true),(137,true),(135,true),(136,true)]
theorem der_79041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79041 :=
  CNF.rup_sound cl_79041 [cl_65890,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65890 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_79042 : CNF.NClause := [(7,true),(125,false),(84,false),(69,false),(126,false),(143,true),(74,false),(76,false),(32,true),(33,true),(86,false)]
theorem der_79042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79042 :=
  CNF.rup_sound cl_79042 [cl_66045,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66045 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79047 : CNF.NClause := [(1056,false),(70,true),(1055,true),(1066,true),(1057,true),(1067,true),(1074,true),(1080,true),(1082,true),(1076,true),(1073,true)]
theorem der_79047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79047 :=
  CNF.rup_sound cl_79047 [cl_71832,cl_54836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71832 v h) (hints_cons _ _ _ (der_54836 v h) (by intro d hd; cases hd)))
def cl_79049 : CNF.NClause := [(1056,false),(1080,true),(1068,true),(1057,true),(1055,true),(1066,true),(1060,true),(71,true),(1082,true),(1076,true),(1073,true)]
theorem der_79049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79049 :=
  CNF.rup_sound cl_79049 [cl_71963,cl_74760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71963 v h) (hints_cons _ _ _ (der_74760 v h) (by intro d hd; cases hd)))
def cl_79050 : CNF.NClause := [(55,true),(148,false),(140,true),(144,true),(80,false),(151,true),(152,true),(132,true),(128,false),(67,false),(18,true)]
theorem der_79050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79050 :=
  CNF.rup_sound cl_79050 [cl_75029,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75029 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_79051 : CNF.NClause := [(139,true),(74,true),(131,true),(151,true),(148,true),(141,true),(152,true),(132,true),(128,false),(135,true),(142,true)]
theorem der_79051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79051 :=
  CNF.rup_sound cl_79051 [cl_75172,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75172 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_79052 : CNF.NClause := [(134,true),(153,true),(71,true),(131,true),(139,true),(137,true),(148,true),(126,true),(152,true),(132,true),(142,true)]
theorem der_79052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79052 :=
  CNF.rup_sound cl_79052 [cl_75217,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75217 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_79067 : CNF.NClause := [(49,false),(34,false),(109,false),(116,false),(101,false),(123,false),(46,false),(54,true),(33,true),(32,false),(106,false),(35,true)]
theorem der_79067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79067 :=
  CNF.rup_sound cl_79067 [cl_55130,cl_64131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55130 v h) (hints_cons _ _ _ (der_64131 v h) (by intro d hd; cases hd)))
def cl_79079 : CNF.NClause := [(900,true),(905,true),(922,true),(916,true),(909,true),(912,true),(925,true),(29,false),(926,true),(80,true),(911,true),(11,true)]
theorem der_79079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79079 :=
  CNF.rup_sound cl_79079 [cl_58011,cl_76959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58011 v h) (hints_cons _ _ _ (der_76959 v h) (by intro d hd; cases hd)))
def cl_79080 : CNF.NClause := [(121,false),(59,false),(137,false),(153,false),(74,false),(101,false),(112,false),(104,false),(62,false),(84,false),(86,false),(78,false)]
theorem der_79080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79080 :=
  CNF.rup_sound cl_79080 [cl_69784,cl_76536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69784 v h) (hints_cons _ _ _ (der_76536 v h) (by intro d hd; cases hd)))
def cl_79081 : CNF.NClause := [(912,true),(922,true),(904,true),(903,true),(909,true),(919,false),(906,true),(29,true),(900,true),(74,true),(910,true),(916,true)]
theorem der_79081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79081 :=
  CNF.rup_sound cl_79081 [cl_69444,cl_75161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69444 v h) (hints_cons _ _ _ (der_75161 v h) (by intro d hd; cases hd)))
def cl_79082 : CNF.NClause := [(904,false),(902,true),(906,true),(79,true),(919,true),(900,true),(26,false),(911,true),(914,true),(912,true),(2,true),(926,true)]
theorem der_79082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79082 :=
  CNF.rup_sound cl_79082 [cl_67343,cl_76600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67343 v h) (hints_cons _ _ _ (der_76600 v h) (by intro d hd; cases hd)))
def cl_79086 : CNF.NClause := [(151,false),(36,true),(131,true),(126,true),(142,true),(84,false),(132,true),(83,false),(130,false),(135,true),(133,true),(86,false)]
theorem der_79086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79086 :=
  CNF.rup_sound cl_79086 [cl_66477,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66477 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_79087 : CNF.NClause := [(113,true),(40,false),(79,false),(76,false),(129,true),(74,false),(70,false),(133,false),(18,false),(131,true),(90,false),(78,false)]
theorem der_79087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79087 :=
  CNF.rup_sound cl_79087 [cl_68331,cl_62957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68331 v h) (hints_cons _ _ _ (der_62957 v h) (by intro d hd; cases hd)))
def cl_79088 : CNF.NClause := [(129,true),(69,false),(136,true),(58,true),(89,false),(88,true),(127,false),(76,false),(62,false),(28,true),(143,true),(78,false)]
theorem der_79088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79088 :=
  CNF.rup_sound cl_79088 [cl_73056,cl_62591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73056 v h) (hints_cons _ _ _ (der_62591 v h) (by intro d hd; cases hd)))
def cl_79092 : CNF.NClause := [(41,true),(134,false),(138,false),(127,true),(133,true),(141,true),(76,false),(131,true),(152,true),(132,true),(73,false),(75,false)]
theorem der_79092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79092 :=
  CNF.rup_sound cl_79092 [cl_71828,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71828 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_79094 : CNF.NClause := [(35,true),(133,true),(131,true),(153,true),(151,true),(137,false),(152,true),(143,true),(83,false),(128,false),(135,true),(142,true)]
theorem der_79094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79094 :=
  CNF.rup_sound cl_79094 [cl_75606,cl_76526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75606 v h) (hints_cons _ _ _ (der_76526 v h) (by intro d hd; cases hd)))
def cl_79097 : CNF.NClause := [(131,false),(88,true),(89,true),(144,true),(141,true),(127,true),(130,true),(138,true),(132,true),(143,true),(135,true),(142,true)]
theorem der_79097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79097 :=
  CNF.rup_sound cl_79097 [cl_75847,cl_8016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75847 v h) (hints_cons _ _ _ (inp_8016 v h) (by intro d hd; cases hd)))
def cl_79098 : CNF.NClause := [(35,false),(120,false),(55,false),(97,false),(111,false),(98,false),(48,true),(106,false),(47,false),(40,false),(46,true),(122,false),(107,false)]
theorem der_79098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79098 :=
  CNF.rup_sound cl_79098 [cl_53084,cl_49851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53084 v h) (hints_cons _ _ _ (der_49851 v h) (by intro d hd; cases hd)))
def cl_79103 : CNF.NClause := [(42,false),(114,false),(116,false),(38,true),(120,false),(103,false),(34,true),(39,true),(32,false),(59,false),(58,false),(100,false),(109,false)]
theorem der_79103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79103 :=
  CNF.rup_sound cl_79103 [cl_55033,cl_64115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55033 v h) (hints_cons _ _ _ (der_64115 v h) (by intro d hd; cases hd)))
def cl_79116 : CNF.NClause := [(139,true),(151,true),(81,false),(137,false),(10,false),(136,false),(68,false),(141,true),(85,false),(128,true),(91,false),(131,true),(43,true)]
theorem der_79116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79116 :=
  CNF.rup_sound cl_79116 [cl_59379,cl_62596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59379 v h) (hints_cons _ _ _ (der_62596 v h) (by intro d hd; cases hd)))
def cl_79118 : CNF.NClause := [(17,true),(34,true),(152,true),(137,true),(135,true),(80,false),(138,true),(127,false),(85,false),(131,true),(65,false),(134,true),(146,false)]
theorem der_79118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79118 :=
  CNF.rup_sound cl_79118 [cl_58336,cl_62576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58336 v h) (hints_cons _ _ _ (der_62576 v h) (by intro d hd; cases hd)))
def cl_79120 : CNF.NClause := [(153,true),(139,true),(134,false),(135,true),(132,true),(33,true),(141,true),(84,false),(79,false),(151,true),(131,true),(126,false),(69,false)]
theorem der_79120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79120 :=
  CNF.rup_sound cl_79120 [cl_60270,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60270 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_79121 : CNF.NClause := [(38,true),(144,true),(64,false),(128,false),(153,true),(89,false),(126,true),(7,false),(71,false),(140,true),(146,true),(80,false),(141,true)]
theorem der_79121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79121 :=
  CNF.rup_sound cl_79121 [cl_61149,cl_76526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61149 v h) (hints_cons _ _ _ (der_76526 v h) (by intro d hd; cases hd)))
def cl_79122 : CNF.NClause := [(153,true),(148,true),(143,true),(130,true),(126,true),(65,false),(44,true),(128,false),(136,false),(147,true),(138,true),(84,false),(135,true)]
theorem der_79122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79122 :=
  CNF.rup_sound cl_79122 [cl_69721,cl_62286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69721 v h) (hints_cons _ _ _ (der_62286 v h) (by intro d hd; cases hd)))
def cl_79125 : CNF.NClause := [(48,false),(95,false),(74,false),(138,false),(108,false),(65,false),(81,false),(119,false),(129,true),(107,false),(23,false),(83,false),(67,false)]
theorem der_79125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79125 :=
  CNF.rup_sound cl_79125 [cl_67541,cl_76534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67541 v h) (hints_cons _ _ _ (der_76534 v h) (by intro d hd; cases hd)))
def cl_79126 : CNF.NClause := [(121,false),(59,false),(77,false),(76,false),(151,false),(85,false),(104,false),(112,false),(140,false),(84,false),(150,true),(101,false),(78,false)]
theorem der_79126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79126 :=
  CNF.rup_sound cl_79126 [cl_67245,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67245 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_79127 : CNF.NClause := [(121,false),(59,false),(83,false),(104,false),(101,false),(65,false),(74,false),(23,false),(93,false),(140,false),(81,false),(141,true),(146,false)]
theorem der_79127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79127 :=
  CNF.rup_sound cl_79127 [cl_69331,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69331 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_79128 : CNF.NClause := [(143,false),(144,true),(133,true),(79,false),(150,true),(137,true),(33,true),(142,true),(151,false),(84,false),(69,false),(135,true),(131,true)]
theorem der_79128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79128 :=
  CNF.rup_sound cl_79128 [cl_69435,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69435 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_79130 : CNF.NClause := [(119,false),(96,false),(69,false),(79,false),(2,false),(103,false),(44,false),(102,false),(84,false),(74,false),(83,false),(128,false),(64,false)]
theorem der_79130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79130 :=
  CNF.rup_sound cl_79130 [cl_73475,cl_76526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73475 v h) (hints_cons _ _ _ (der_76526 v h) (by intro d hd; cases hd)))
def cl_79131 : CNF.NClause := [(26,false),(900,true),(912,true),(902,true),(21,true),(908,true),(916,true),(79,true),(901,true),(921,true),(927,true),(918,true),(917,true)]
theorem der_79131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79131 :=
  CNF.rup_sound cl_79131 [cl_73256,cl_76540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73256 v h) (hints_cons _ _ _ (der_76540 v h) (by intro d hd; cases hd)))
def cl_79133 : CNF.NClause := [(15,false),(105,true),(54,false),(153,true),(12,false),(84,false),(69,false),(134,true),(143,true),(78,false),(147,false),(127,false),(131,true)]
theorem der_79133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79133 :=
  CNF.rup_sound cl_79133 [cl_70340,cl_76537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70340 v h) (hints_cons _ _ _ (der_76537 v h) (by intro d hd; cases hd)))
def cl_79134 : CNF.NClause := [(911,true),(920,true),(126,false),(33,true),(909,true),(74,false),(916,true),(79,false),(69,false),(131,true),(921,true),(927,true),(917,true)]
theorem der_79134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79134 :=
  CNF.rup_sound cl_79134 [cl_72070,cl_62575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72070 v h) (hints_cons _ _ _ (der_62575 v h) (by intro d hd; cases hd)))
def cl_79136 : CNF.NClause := [(15,false),(115,true),(3,false),(148,true),(126,true),(44,false),(68,false),(137,false),(28,true),(83,false),(85,false),(89,false),(146,false)]
theorem der_79136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79136 :=
  CNF.rup_sound cl_79136 [cl_70279,cl_15793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70279 v h) (hints_cons _ _ _ (der_15793 v h) (by intro d hd; cases hd)))
def cl_79138 : CNF.NClause := [(105,false),(24,false),(85,false),(106,false),(104,false),(41,false),(76,false),(123,false),(136,false),(84,false),(80,false),(128,false),(146,false)]
theorem der_79138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79138 :=
  CNF.rup_sound cl_79138 [cl_74562,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74562 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_79145 : CNF.NClause := [(27,false),(1060,true),(1074,true),(1058,true),(1057,true),(1055,true),(1064,true),(76,true),(1073,true),(1082,true),(1062,true),(1065,true),(1072,true)]
theorem der_79145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79145 :=
  CNF.rup_sound cl_79145 [cl_76297,cl_15742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76297 v h) (hints_cons _ _ _ (der_15742 v h) (by intro d hd; cases hd)))
def cl_79150 : CNF.NClause := [(59,false),(55,true),(66,false),(116,false),(92,false),(117,false),(41,false),(65,false),(113,false),(114,false),(90,false),(36,false),(73,false),(84,false)]
theorem der_79150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79150 :=
  CNF.rup_sound cl_79150 [cl_40056,cl_78158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40056 v h) (hints_cons _ _ _ (der_78158 v h) (by intro d hd; cases hd)))
def cl_79154 : CNF.NClause := [(123,false),(51,false),(73,false),(98,false),(81,false),(83,false),(78,false),(4,false),(87,false),(68,false),(101,false),(88,false),(40,false),(102,false)]
theorem der_79154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79154 :=
  CNF.rup_sound cl_79154 [cl_53117,cl_77069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53117 v h) (hints_cons _ _ _ (der_77069 v h) (by intro d hd; cases hd)))
def cl_79156 : CNF.NClause := [(17,true),(153,false),(60,false),(67,false),(99,true),(128,true),(84,false),(132,true),(136,true),(89,false),(75,false),(10,false),(69,false),(71,false)]
theorem der_79156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79156 :=
  CNF.rup_sound cl_79156 [cl_59743,cl_61595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59743 v h) (hints_cons _ _ _ (der_61595 v h) (by intro d hd; cases hd)))
def cl_79157 : CNF.NClause := [(110,true),(52,false),(137,true),(2,false),(69,false),(76,false),(68,false),(142,false),(74,false),(84,false),(79,false),(147,true),(28,false),(64,false)]
theorem der_79157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79157 :=
  CNF.rup_sound cl_79157 [cl_58850,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58850 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_79159 : CNF.NClause := [(120,false),(1,false),(101,false),(81,false),(2,false),(44,false),(76,false),(66,false),(84,false),(86,false),(94,false),(78,false),(110,false),(45,false)]
theorem der_79159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79159 :=
  CNF.rup_sound cl_79159 [cl_65112,cl_77554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65112 v h) (hints_cons _ _ _ (der_77554 v h) (by intro d hd; cases hd)))
def cl_79160 : CNF.NClause := [(48,false),(16,false),(151,false),(85,false),(60,false),(44,false),(3,false),(76,false),(84,false),(43,false),(6,false),(68,false),(77,false),(40,false)]
theorem der_79160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79160 :=
  CNF.rup_sound cl_79160 [cl_65480,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65480 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_79161 : CNF.NClause := [(108,false),(3,false),(141,false),(48,false),(65,false),(80,false),(71,false),(119,false),(114,false),(85,false),(95,false),(125,false),(86,false),(75,false)]
theorem der_79161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79161 :=
  CNF.rup_sound cl_79161 [cl_67490,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67490 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79162 : CNF.NClause := [(9,true),(140,true),(153,true),(76,false),(63,false),(3,false),(136,false),(43,false),(83,false),(73,false),(144,true),(99,true),(90,false),(78,false)]
theorem der_79162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79162 :=
  CNF.rup_sound cl_79162 [cl_65683,cl_77008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65683 v h) (hints_cons _ _ _ (der_77008 v h) (by intro d hd; cases hd)))
def cl_79165 : CNF.NClause := [(48,false),(101,false),(1,false),(66,false),(81,false),(108,false),(119,false),(128,false),(71,false),(95,false),(76,false),(83,false),(86,false),(78,false)]
theorem der_79165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79165 :=
  CNF.rup_sound cl_79165 [cl_67449,cl_62171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67449 v h) (hints_cons _ _ _ (der_62171 v h) (by intro d hd; cases hd)))
def cl_79166 : CNF.NClause := [(34,false),(116,false),(7,true),(137,false),(65,false),(118,false),(106,false),(153,false),(84,false),(152,true),(11,true),(101,false),(86,false),(78,false)]
theorem der_79166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79166 :=
  CNF.rup_sound cl_79166 [cl_68984,cl_62596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68984 v h) (hints_cons _ _ _ (der_62596 v h) (by intro d hd; cases hd)))
def cl_79167 : CNF.NClause := [(93,false),(126,false),(69,false),(119,false),(128,false),(117,false),(60,false),(79,false),(73,false),(74,false),(83,false),(111,false),(131,true),(78,false)]
theorem der_79167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79167 :=
  CNF.rup_sound cl_79167 [cl_66744,cl_62575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66744 v h) (hints_cons _ _ _ (der_62575 v h) (by intro d hd; cases hd)))
def cl_79169 : CNF.NClause := [(48,false),(95,false),(85,false),(144,false),(108,false),(107,false),(68,false),(119,false),(84,false),(83,false),(70,false),(129,false),(86,false),(67,false)]
theorem der_79169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79169 :=
  CNF.rup_sound cl_79169 [cl_66918,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66918 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_79170 : CNF.NClause := [(107,false),(94,false),(84,false),(70,false),(80,false),(85,false),(126,false),(65,false),(3,false),(122,false),(55,false),(98,false),(131,true),(75,false)]
theorem der_79170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79170 :=
  CNF.rup_sound cl_79170 [cl_68926,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68926 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_79171 : CNF.NClause := [(151,false),(140,false),(55,false),(85,false),(111,false),(141,true),(98,false),(84,false),(76,false),(94,false),(68,false),(122,false),(78,false),(75,false)]
theorem der_79171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79171 :=
  CNF.rup_sound cl_79171 [cl_68295,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68295 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_79173 : CNF.NClause := [(93,false),(130,false),(100,false),(74,false),(120,false),(58,false),(107,false),(68,false),(72,false),(81,false),(12,false),(85,false),(64,false),(78,false)]
theorem der_79173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79173 :=
  CNF.rup_sound cl_79173 [cl_70933,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70933 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_79176 : CNF.NClause := [(35,false),(99,false),(82,false),(85,false),(109,false),(5,false),(118,false),(94,false),(134,false),(76,false),(84,false),(83,false),(73,false),(146,false)]
theorem der_79176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79176 :=
  CNF.rup_sound cl_79176 [cl_74428,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74428 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_79178 : CNF.NClause := [(44,false),(125,false),(52,false),(94,false),(141,true),(80,false),(38,false),(70,false),(65,false),(85,false),(45,false),(3,false),(71,false),(146,false)]
theorem der_79178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79178 :=
  CNF.rup_sound cl_79178 [cl_72466,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72466 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79180 : CNF.NClause := [(1080,false),(1071,true),(35,true),(1067,true),(1059,true),(1075,true),(1063,true),(1081,true),(1076,true),(1073,true),(83,false),(128,false),(1065,true),(1072,true)]
theorem der_79180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79180 :=
  CNF.rup_sound cl_79180 [cl_74268,cl_76526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74268 v h) (hints_cons _ _ _ (der_76526 v h) (by intro d hd; cases hd)))
def cl_79181 : CNF.NClause := [(37,true),(125,false),(138,true),(74,false),(141,false),(127,true),(144,true),(82,false),(131,true),(137,true),(70,false),(152,true),(143,true),(78,false)]
theorem der_79181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79181 :=
  CNF.rup_sound cl_79181 [cl_74929,cl_56933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74929 v h) (hints_cons _ _ _ (der_56933 v h) (by intro d hd; cases hd)))
def cl_79184 : CNF.NClause := [(916,true),(925,true),(903,true),(914,true),(909,true),(901,true),(919,true),(911,true),(923,true),(900,true),(927,true),(907,true),(910,true),(917,true)]
theorem der_79184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79184 :=
  CNF.rup_sound cl_79184 [cl_76079,cl_15716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76079 v h) (hints_cons _ _ _ (der_15716 v h) (by intro d hd; cases hd)))
def cl_79192 : CNF.NClause := [(95,false),(36,false),(83,false),(5,false),(105,false),(72,false),(63,false),(70,false),(118,false),(33,false),(89,false),(82,false),(100,false),(79,false),(14,false)]
theorem der_79192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79192 :=
  CNF.rup_sound cl_79192 [cl_37550,cl_77677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37550 v h) (hints_cons _ _ _ (der_77677 v h) (by intro d hd; cases hd)))
def cl_79193 : CNF.NClause := [(43,false),(12,false),(115,false),(90,false),(34,true),(87,false),(33,false),(35,false),(105,false),(68,false),(85,false),(110,false),(81,false),(92,false),(100,false)]
theorem der_79193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79193 :=
  CNF.rup_sound cl_79193 [cl_54992,cl_77102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54992 v h) (hints_cons _ _ _ (der_77102 v h) (by intro d hd; cases hd)))
def cl_79197 : CNF.NClause := [(20,false),(16,false),(118,false),(89,false),(15,false),(1,false),(34,false),(75,false),(111,false),(67,false),(96,false),(69,false),(70,false),(84,false),(116,false)]
theorem der_79197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79197 :=
  CNF.rup_sound cl_79197 [cl_44300,cl_76570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44300 v h) (hints_cons _ _ _ (der_76570 v h) (by intro d hd; cases hd)))
def cl_79199 : CNF.NClause := [(114,false),(109,false),(76,false),(69,false),(104,false),(91,false),(33,false),(35,false),(79,false),(24,false),(80,false),(99,false),(74,false),(67,false),(63,false)]
theorem der_79199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79199 :=
  CNF.rup_sound cl_79199 [cl_64307,cl_51112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64307 v h) (hints_cons _ _ _ (der_51112 v h) (by intro d hd; cases hd)))
def cl_79202 : CNF.NClause := [(59,false),(55,true),(108,false),(119,false),(109,false),(94,false),(48,false),(102,false),(43,true),(101,false),(44,false),(103,false),(54,false),(50,false),(121,false)]
theorem der_79202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79202 :=
  CNF.rup_sound cl_79202 [cl_54142,cl_49931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54142 v h) (hints_cons _ _ _ (der_49931 v h) (by intro d hd; cases hd)))
def cl_79203 : CNF.NClause := [(29,false),(27,false),(112,false),(70,false),(89,false),(113,false),(80,false),(34,false),(119,false),(78,false),(69,false),(75,false),(40,false),(94,false),(76,false)]
theorem der_79203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79203 :=
  CNF.rup_sound cl_79203 [cl_54691,cl_77998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54691 v h) (hints_cons _ _ _ (der_77998 v h) (by intro d hd; cases hd)))
def cl_79204 : CNF.NClause := [(47,false),(109,false),(77,false),(85,false),(46,false),(83,false),(75,false),(5,false),(111,false),(86,false),(110,false),(112,false),(89,false),(82,false),(92,false)]
theorem der_79204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79204 :=
  CNF.rup_sound cl_79204 [cl_64374,cl_51626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64374 v h) (hints_cons _ _ _ (der_51626 v h) (by intro d hd; cases hd)))
def cl_79205 : CNF.NClause := [(102,false),(92,false),(84,false),(81,false),(119,false),(68,false),(103,false),(140,false),(79,false),(15,false),(96,false),(44,false),(78,false),(3,false),(89,false)]
theorem der_79205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79205 :=
  CNF.rup_sound cl_79205 [cl_56401,cl_43611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56401 v h) (hints_cons _ _ _ (der_43611 v h) (by intro d hd; cases hd)))
def cl_79212 : CNF.NClause := [(42,false),(54,false),(81,false),(78,false),(84,false),(88,false),(13,false),(74,false),(111,false),(121,false),(97,false),(89,false),(100,false),(72,false),(71,false)]
theorem der_79212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79212 :=
  CNF.rup_sound cl_79212 [cl_61171,cl_77748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61171 v h) (hints_cons _ _ _ (der_77748 v h) (by intro d hd; cases hd)))
def cl_79213 : CNF.NClause := [(50,false),(59,false),(71,false),(100,false),(54,true),(44,false),(151,false),(76,false),(7,false),(85,false),(9,false),(48,false),(64,false),(73,false),(80,false)]
theorem der_79213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79213 :=
  CNF.rup_sound cl_79213 [cl_65500,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65500 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_79215 : CNF.NClause := [(122,false),(115,false),(80,false),(128,false),(73,false),(70,false),(3,false),(85,false),(63,false),(83,false),(65,false),(107,false),(98,false),(55,false),(75,false)]
theorem der_79215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79215 :=
  CNF.rup_sound cl_79215 [cl_65699,cl_62286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65699 v h) (hints_cons _ _ _ (der_62286 v h) (by intro d hd; cases hd)))
def cl_79218 : CNF.NClause := [(95,false),(99,false),(85,false),(112,false),(43,false),(74,false),(83,false),(5,false),(122,false),(82,false),(134,false),(84,false),(73,false),(86,false),(75,false)]
theorem der_79218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79218 :=
  CNF.rup_sound cl_79218 [cl_69851,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69851 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_79219 : CNF.NClause := [(50,false),(121,false),(108,false),(102,false),(83,false),(84,false),(128,false),(116,false),(79,false),(45,true),(63,false),(74,false),(126,false),(69,false),(131,true)]
theorem der_79219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79219 :=
  CNF.rup_sound cl_79219 [cl_66472,cl_62286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66472 v h) (hints_cons _ _ _ (der_62286 v h) (by intro d hd; cases hd)))
def cl_79220 : CNF.NClause := [(109,false),(117,false),(98,false),(77,false),(72,false),(85,false),(12,false),(121,false),(91,false),(89,false),(150,true),(81,false),(140,false),(64,false),(53,false)]
theorem der_79220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79220 :=
  CNF.rup_sound cl_79220 [cl_66186,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66186 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_79221 : CNF.NClause := [(103,false),(110,false),(85,false),(3,false),(65,false),(128,false),(80,false),(120,false),(63,false),(45,false),(70,false),(83,false),(117,false),(73,false),(75,false)]
theorem der_79221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79221 :=
  CNF.rup_sound cl_79221 [cl_69139,cl_62286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69139 v h) (hints_cons _ _ _ (der_62286 v h) (by intro d hd; cases hd)))
def cl_79222 : CNF.NClause := [(106,false),(95,false),(71,false),(109,false),(121,false),(129,false),(83,false),(70,false),(84,false),(68,false),(20,false),(69,false),(86,false),(53,false),(67,false)]
theorem der_79222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79222 :=
  CNF.rup_sound cl_79222 [cl_67799,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67799 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_79224 : CNF.NClause := [(20,false),(129,false),(106,false),(71,false),(69,false),(111,false),(67,false),(96,false),(83,false),(68,false),(70,false),(84,false),(34,false),(86,false),(118,false)]
theorem der_79224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79224 :=
  CNF.rup_sound cl_79224 [cl_68071,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68071 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_79225 : CNF.NClause := [(113,false),(125,false),(79,false),(94,false),(69,false),(126,false),(84,false),(71,false),(40,false),(76,false),(119,false),(106,false),(74,false),(131,true),(86,false)]
theorem der_79225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79225 :=
  CNF.rup_sound cl_79225 [cl_68385,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68385 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79226 : CNF.NClause := [(95,false),(99,false),(69,false),(65,false),(71,false),(63,false),(137,false),(82,false),(122,false),(81,false),(43,false),(116,false),(9,false),(78,false),(75,false)]
theorem der_79226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79226 :=
  CNF.rup_sound cl_79226 [cl_68093,cl_61980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68093 v h) (hints_cons _ _ _ (der_61980 v h) (by intro d hd; cases hd)))
def cl_79228 : CNF.NClause := [(38,true),(125,false),(80,false),(119,false),(76,false),(65,false),(71,false),(109,false),(127,false),(85,false),(103,false),(115,false),(44,false),(86,false),(75,false)]
theorem der_79228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79228 :=
  CNF.rup_sound cl_79228 [cl_68222,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68222 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79229 : CNF.NClause := [(902,true),(911,true),(908,true),(904,true),(928,true),(35,true),(926,true),(916,true),(921,true),(927,true),(907,true),(83,false),(128,false),(910,true),(917,true)]
theorem der_79229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79229 :=
  CNF.rup_sound cl_79229 [cl_74310,cl_76526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74310 v h) (hints_cons _ _ _ (der_76526 v h) (by intro d hd; cases hd)))
def cl_79230 : CNF.NClause := [(38,true),(130,false),(33,false),(12,false),(85,false),(74,false),(68,false),(100,false),(64,false),(72,false),(118,false),(115,false),(81,false),(110,false),(78,false)]
theorem der_79230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79230 :=
  CNF.rup_sound cl_79230 [cl_70306,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70306 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_79231 : CNF.NClause := [(4,false),(105,false),(98,false),(63,false),(68,false),(112,false),(127,false),(83,false),(54,false),(120,false),(85,false),(80,false),(78,false),(73,false),(75,false)]
theorem der_79231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79231 :=
  CNF.rup_sound cl_79231 [cl_73189,cl_62580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73189 v h) (hints_cons _ _ _ (der_62580 v h) (by intro d hd; cases hd)))
def cl_79232 : CNF.NClause := [(43,true),(139,true),(85,false),(134,true),(141,true),(136,false),(81,false),(129,true),(140,true),(137,true),(152,true),(143,true),(128,true),(135,true),(146,false)]
theorem der_79232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79232 :=
  CNF.rup_sound cl_79232 [cl_73345,cl_69142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73345 v h) (hints_cons _ _ _ (der_69142 v h) (by intro d hd; cases hd)))
def cl_79233 : CNF.NClause := [(108,false),(99,false),(125,false),(85,false),(80,false),(76,false),(71,false),(65,false),(70,false),(3,false),(42,true),(115,false),(120,false),(47,false),(146,false)]
theorem der_79233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79233 :=
  CNF.rup_sound cl_79233 [cl_70409,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70409 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79234 : CNF.NClause := [(99,false),(5,false),(84,false),(74,false),(93,false),(85,false),(60,false),(119,false),(49,true),(134,false),(111,false),(82,false),(83,false),(73,false),(146,false)]
theorem der_79234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79234 :=
  CNF.rup_sound cl_79234 [cl_74555,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74555 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_79235 : CNF.NClause := [(29,false),(94,false),(127,false),(89,false),(125,false),(69,false),(81,false),(40,false),(119,false),(76,false),(113,false),(27,false),(71,false),(78,false),(146,false)]
theorem der_79235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79235 :=
  CNF.rup_sound cl_79235 [cl_71065,cl_62591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71065 v h) (hints_cons _ _ _ (der_62591 v h) (by intro d hd; cases hd)))
def cl_79237 : CNF.NClause := [(4,false),(125,false),(68,false),(63,false),(113,false),(115,false),(76,false),(71,false),(116,false),(83,false),(123,false),(78,false),(36,false),(73,false),(86,false)]
theorem der_79237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79237 :=
  CNF.rup_sound cl_79237 [cl_74125,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74125 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79238 : CNF.NClause := [(105,false),(123,false),(104,false),(39,true),(127,false),(41,false),(80,false),(85,false),(81,false),(48,true),(70,false),(103,false),(125,false),(71,false),(146,false)]
theorem der_79238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79238 :=
  CNF.rup_sound cl_79238 [cl_73186,cl_76525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73186 v h) (hints_cons _ _ _ (der_76525 v h) (by intro d hd; cases hd)))
def cl_79239 : CNF.NClause := [(35,true),(151,true),(150,true),(127,true),(133,false),(138,true),(141,true),(140,true),(152,true),(132,true),(143,true),(83,false),(128,false),(135,true),(142,true)]
theorem der_79239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79239 :=
  CNF.rup_sound cl_79239 [cl_75624,cl_76526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75624 v h) (hints_cons _ _ _ (der_76526 v h) (by intro d hd; cases hd)))
def cl_79248 : CNF.NClause := [(29,false),(27,false),(9,false),(75,false),(63,false),(118,false),(85,false),(96,false),(82,false),(78,false),(34,false),(111,false),(89,false),(81,false),(101,false),(76,false)]
theorem der_79248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79248 :=
  CNF.rup_sound cl_79248 [cl_53177,cl_76916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53177 v h) (hints_cons _ _ _ (der_76916 v h) (by intro d hd; cases hd)))
def cl_79251 : CNF.NClause := [(106,false),(77,false),(118,false),(92,false),(15,false),(73,false),(50,true),(81,false),(52,false),(80,false),(101,false),(67,false),(88,false),(96,false),(34,false),(78,false)]
theorem der_79251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79251 :=
  CNF.rup_sound cl_79251 [cl_47945,cl_78427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47945 v h) (hints_cons _ _ _ (der_78427 v h) (by intro d hd; cases hd)))
def cl_79252 : CNF.NClause := [(110,false),(12,false),(67,false),(113,false),(72,false),(90,false),(96,false),(22,false),(9,false),(39,false),(86,false),(85,false),(68,false),(78,false),(107,false),(91,false)]
theorem der_79252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79252 :=
  CNF.rup_sound cl_79252 [cl_54750,cl_76604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54750 v h) (hints_cons _ _ _ (der_76604 v h) (by intro d hd; cases hd)))
def cl_79254 : CNF.NClause := [(97,true),(5,true),(81,false),(89,false),(15,false),(28,true),(75,false),(71,false),(1,false),(76,false),(68,false),(86,false),(13,true),(37,false),(66,false),(148,false)]
theorem der_79254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79254 :=
  CNF.rup_sound cl_79254 [cl_57707,cl_76765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57707 v h) (hints_cons _ _ _ (der_76765 v h) (by intro d hd; cases hd)))
def cl_79255 : CNF.NClause := [(17,true),(82,false),(75,false),(69,false),(86,false),(63,false),(68,false),(119,true),(81,false),(52,false),(21,false),(28,false),(13,true),(88,false),(80,false),(74,false)]
theorem der_79255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79255 :=
  CNF.rup_sound cl_79255 [cl_58861,cl_64359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58861 v h) (hints_cons _ _ _ (der_64359 v h) (by intro d hd; cases hd)))
def cl_79256 : CNF.NClause := [(101,false),(57,true),(84,false),(69,false),(125,false),(141,true),(99,false),(71,false),(2,false),(64,false),(86,false),(51,false),(79,false),(74,false),(123,false),(53,false)]
theorem der_79256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79256 :=
  CNF.rup_sound cl_79256 [cl_57916,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57916 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_79257 : CNF.NClause := [(20,false),(70,false),(146,true),(82,false),(151,false),(81,false),(80,false),(58,false),(74,false),(66,false),(78,false),(128,true),(79,false),(18,false),(109,true),(137,true)]
theorem der_79257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79257 :=
  CNF.rup_sound cl_79257 [cl_58357,cl_49957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58357 v h) (hints_cons _ _ _ (der_49957 v h) (by intro d hd; cases hd)))
def cl_79262 : CNF.NClause := [(121,false),(59,false),(85,false),(81,false),(125,false),(76,false),(71,false),(104,false),(115,false),(54,true),(70,false),(75,false),(80,false),(93,false),(65,false),(3,false)]
theorem der_79262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79262 :=
  CNF.rup_sound cl_79262 [cl_62678,cl_56933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62678 v h) (hints_cons _ _ _ (der_56933 v h) (by intro d hd; cases hd)))
def cl_79265 : CNF.NClause := [(139,false),(99,false),(76,false),(72,false),(117,false),(119,false),(79,false),(10,false),(78,false),(73,false),(93,false),(75,false),(141,true),(74,false),(81,false),(60,false)]
theorem der_79265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79265 :=
  CNF.rup_sound cl_79265 [cl_59909,cl_62452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59909 v h) (hints_cons _ _ _ (der_62452 v h) (by intro d hd; cases hd)))
def cl_79266 : CNF.NClause := [(36,false),(92,false),(63,false),(13,false),(9,false),(44,false),(10,false),(69,false),(81,false),(74,false),(52,false),(82,false),(105,false),(55,false),(73,false),(76,false)]
theorem der_79266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79266 :=
  CNF.rup_sound cl_79266 [cl_65428,cl_35284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65428 v h) (hints_cons _ _ _ (der_35284 v h) (by intro d hd; cases hd)))
def cl_79267 : CNF.NClause := [(113,false),(1,false),(81,false),(66,false),(119,false),(76,false),(71,false),(74,false),(126,false),(84,false),(40,false),(94,false),(106,false),(69,false),(131,true),(86,false)]
theorem der_79267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79267 :=
  CNF.rup_sound cl_79267 [cl_67920,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67920 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_79279 : CNF.NClause := [(20,false),(68,false),(129,false),(38,false),(57,false),(69,false),(55,false),(42,true),(83,false),(45,false),(39,true),(116,false),(70,false),(84,false),(71,false),(146,false)]
theorem der_79279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79279 :=
  CNF.rup_sound cl_79279 [cl_73246,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73246 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_79280 : CNF.NClause := [(40,true),(5,false),(102,false),(85,false),(134,false),(110,false),(82,false),(83,false),(42,true),(57,false),(122,false),(74,false),(93,false),(84,false),(73,false),(146,false)]
theorem der_79280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79280 :=
  CNF.rup_sound cl_79280 [cl_73063,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73063 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_79284 : CNF.NClause := [(42,false),(121,false),(64,false),(123,false),(82,false),(35,false),(7,true),(79,false),(107,false),(74,false),(73,false),(69,false),(84,false),(2,false),(34,false),(41,false),(87,false)]
theorem der_79284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79284 :=
  CNF.rup_sound cl_79284 [cl_55057,cl_41521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55057 v h) (hints_cons _ _ _ (der_41521 v h) (by intro d hd; cases hd)))
def cl_79287 : CNF.NClause := [(4,false),(87,false),(63,false),(98,false),(112,false),(96,false),(68,false),(28,true),(13,false),(120,false),(92,false),(54,false),(75,false),(76,false),(74,false),(83,false),(10,false)]
theorem der_79287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79287 :=
  CNF.rup_sound cl_79287 [cl_47612,cl_76963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47612 v h) (hints_cons _ _ _ (der_76963 v h) (by intro d hd; cases hd)))
def cl_79288 : CNF.NClause := [(102,false),(6,false),(2,false),(85,false),(68,false),(12,false),(96,false),(42,true),(79,false),(109,false),(69,false),(72,false),(84,false),(44,false),(87,false),(119,false),(81,false)]
theorem der_79288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79288 :=
  CNF.rup_sound cl_79288 [cl_64320,cl_42426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64320 v h) (hints_cons _ _ _ (der_42426 v h) (by intro d hd; cases hd)))
def cl_79289 : CNF.NClause := [(121,false),(93,false),(59,false),(75,false),(13,false),(112,false),(69,false),(74,false),(48,true),(70,false),(20,false),(73,false),(10,false),(115,false),(76,false),(68,false),(67,false)]
theorem der_79289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79289 :=
  CNF.rup_sound cl_79289 [cl_54656,cl_76795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54656 v h) (hints_cons _ _ _ (der_76795 v h) (by intro d hd; cases hd)))
def cl_79290 : CNF.NClause := [(121,false),(59,false),(139,false),(93,false),(73,false),(10,false),(75,false),(141,true),(13,false),(76,false),(79,false),(101,false),(78,false),(115,false),(81,false),(74,false),(18,true)]
theorem der_79290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79290 :=
  CNF.rup_sound cl_79290 [cl_54619,cl_62452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54619 v h) (hints_cons _ _ _ (der_62452 v h) (by intro d hd; cases hd)))
def cl_79291 : CNF.NClause := [(52,true),(92,false),(82,false),(106,false),(3,false),(74,false),(83,false),(34,false),(35,true),(111,false),(22,false),(69,false),(2,false),(96,false),(79,false),(5,false),(101,false)]
theorem der_79291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79291 :=
  CNF.rup_sound cl_79291 [cl_64341,cl_48797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64341 v h) (hints_cons _ _ _ (der_48797 v h) (by intro d hd; cases hd)))
def cl_79300 : CNF.NClause := [(119,false),(68,false),(60,false),(71,false),(63,false),(93,false),(77,false),(65,false),(19,false),(85,false),(117,false),(132,false),(90,false),(54,true),(76,false),(111,false),(74,false)]
theorem der_79300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79300 :=
  CNF.rup_sound cl_79300 [cl_57473,cl_63081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57473 v h) (hints_cons _ _ _ (der_63081 v h) (by intro d hd; cases hd)))
def cl_79302 : CNF.NClause := [(121,false),(98,false),(74,false),(38,true),(85,false),(109,false),(117,false),(28,false),(2,false),(65,false),(53,false),(69,false),(3,false),(64,false),(75,false),(80,false),(79,false)]
theorem der_79302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79302 :=
  CNF.rup_sound cl_79302 [cl_57296,cl_49686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57296 v h) (hints_cons _ _ _ (der_49686 v h) (by intro d hd; cases hd)))
def cl_79303 : CNF.NClause := [(5,true),(36,true),(82,false),(66,false),(78,false),(142,false),(58,false),(73,false),(77,false),(104,false),(47,false),(69,false),(6,false),(70,false),(60,false),(96,false),(74,false)]
theorem der_79303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79303 :=
  CNF.rup_sound cl_79303 [cl_64857,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64857 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_79304 : CNF.NClause := [(58,false),(44,true),(6,false),(66,false),(93,false),(107,false),(120,false),(73,false),(70,false),(69,false),(5,true),(78,false),(82,false),(142,false),(77,false),(74,false),(116,false)]
theorem der_79304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79304 :=
  CNF.rup_sound cl_79304 [cl_58479,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58479 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_79309 : CNF.NClause := [(105,false),(92,false),(78,false),(112,false),(54,false),(98,false),(82,false),(83,false),(5,false),(88,false),(3,false),(71,false),(72,false),(86,false),(120,false),(85,false),(13,false)]
theorem der_79309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79309 :=
  CNF.rup_sound cl_79309 [cl_61651,cl_49766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61651 v h) (hints_cons _ _ _ (der_49766 v h) (by intro d hd; cases hd)))
def cl_79310 : CNF.NClause := [(17,false),(117,false),(77,false),(64,false),(111,false),(29,false),(99,false),(85,false),(78,false),(83,false),(105,false),(89,false),(60,false),(27,false),(69,false),(44,true),(70,false)]
theorem der_79310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79310 :=
  CNF.rup_sound cl_79310 [cl_60537,cl_76553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60537 v h) (hints_cons _ _ _ (der_76553 v h) (by intro d hd; cases hd)))
def cl_79312 : CNF.NClause := [(59,false),(121,false),(12,false),(101,false),(71,false),(104,false),(83,false),(115,false),(85,false),(26,false),(68,false),(75,false),(54,true),(64,false),(79,false),(72,false),(28,false)]
theorem der_79312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79312 :=
  CNF.rup_sound cl_79312 [cl_61501,cl_76603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61501 v h) (hints_cons _ _ _ (der_76603 v h) (by intro d hd; cases hd)))
def cl_79314 : CNF.NClause := [(100,false),(95,false),(71,false),(90,false),(89,false),(85,false),(63,false),(139,true),(33,false),(74,false),(84,false),(141,true),(75,false),(118,false),(140,false),(142,true),(110,false)]
theorem der_79314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79314 :=
  CNF.rup_sound cl_79314 [cl_61064,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61064 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_79315 : CNF.NClause := [(50,false),(116,false),(105,false),(1,false),(94,false),(3,false),(83,false),(76,false),(77,false),(121,false),(17,false),(38,true),(81,false),(66,false),(153,false),(64,false),(71,false)]
theorem der_79315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79315 :=
  CNF.rup_sound cl_79315 [cl_63052,cl_54024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63052 v h) (hints_cons _ _ _ (der_54024 v h) (by intro d hd; cases hd)))
def cl_79322 : CNF.NClause := [(92,false),(83,false),(20,false),(109,false),(91,false),(68,false),(62,false),(26,false),(58,false),(116,false),(79,false),(70,false),(120,false),(107,false),(40,true),(69,false),(146,false)]
theorem der_79322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79322 :=
  CNF.rup_sound cl_79322 [cl_67834,cl_42754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67834 v h) (hints_cons _ _ _ (der_42754 v h) (by intro d hd; cases hd)))
def cl_79323 : CNF.NClause := [(49,false),(33,false),(1,false),(57,false),(23,false),(89,false),(76,false),(74,false),(71,false),(120,false),(83,false),(66,false),(65,false),(2,false),(86,false),(53,false),(67,false)]
theorem der_79323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79323 :=
  CNF.rup_sound cl_79323 [cl_68652,cl_76824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68652 v h) (hints_cons _ _ _ (der_76824 v h) (by intro d hd; cases hd)))
def cl_79327 : CNF.NClause := [(37,false),(43,false),(68,false),(20,false),(69,false),(57,false),(129,false),(49,true),(38,true),(42,true),(84,false),(55,false),(70,false),(60,false),(71,false),(83,false),(146,false)]
theorem der_79327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79327 :=
  CNF.rup_sound cl_79327 [cl_70634,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70634 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_79330 : CNF.NClause := [(42,false),(34,true),(83,false),(67,false),(40,false),(78,false),(52,false),(47,false),(115,false),(108,false),(72,false),(120,false),(22,false),(99,false),(69,false),(75,false),(64,false),(86,false)]
theorem der_79330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79330 :=
  CNF.rup_sound cl_79330 [cl_53219,cl_77086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53219 v h) (hints_cons _ _ _ (der_77086 v h) (by intro d hd; cases hd)))
def cl_79335 : CNF.NClause := [(27,false),(54,false),(98,false),(89,false),(26,false),(78,false),(83,false),(96,false),(69,false),(71,false),(112,false),(105,false),(24,false),(85,false),(79,false),(12,false),(75,false),(48,true)]
theorem der_79335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79335 :=
  CNF.rup_sound cl_79335 [cl_64284,cl_57423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64284 v h) (hints_cons _ _ _ (der_57423 v h) (by intro d hd; cases hd)))
def cl_79338 : CNF.NClause := [(27,false),(62,false),(82,false),(101,false),(89,false),(9,false),(85,false),(81,false),(88,false),(118,false),(34,false),(78,false),(111,false),(53,true),(76,false),(75,false),(63,false),(96,false)]
theorem der_79338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79338 :=
  CNF.rup_sound cl_79338 [cl_44386,cl_76916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44386 v h) (hints_cons _ _ _ (der_76916 v h) (by intro d hd; cases hd)))
def cl_79341 : CNF.NClause := [(101,false),(8,false),(28,true),(75,false),(78,false),(48,false),(119,false),(65,false),(22,false),(64,false),(114,false),(20,false),(41,true),(86,false),(82,false),(76,false),(108,false),(79,false)]
theorem der_79341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79341 :=
  CNF.rup_sound cl_79341 [cl_55728,cl_56202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55728 v h) (hints_cons _ _ _ (der_56202 v h) (by intro d hd; cases hd)))
def cl_79346 : CNF.NClause := [(104,false),(6,false),(131,true),(141,true),(74,false),(78,false),(70,false),(82,false),(119,false),(72,false),(110,false),(85,false),(66,false),(52,false),(98,false),(136,false),(81,false),(10,false)]
theorem der_79346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79346 :=
  CNF.rup_sound cl_79346 [cl_57376,cl_69142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57376 v h) (hints_cons _ _ _ (der_69142 v h) (by intro d hd; cases hd)))
def cl_79350 : CNF.NClause := [(42,false),(52,true),(6,false),(66,false),(121,false),(68,false),(73,false),(100,false),(103,false),(63,false),(87,false),(4,false),(83,false),(74,false),(70,false),(82,false),(111,false),(18,false)]
theorem der_79350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79350 :=
  CNF.rup_sound cl_79350 [cl_62274,cl_76796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62274 v h) (hints_cons _ _ _ (der_76796 v h) (by intro d hd; cases hd)))
def cl_79354 : CNF.NClause := [(153,true),(112,false),(151,false),(119,false),(126,true),(91,false),(138,true),(89,false),(71,false),(94,false),(85,false),(40,false),(113,false),(83,false),(78,false),(76,false),(152,true),(75,false)]
theorem der_79354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79354 :=
  CNF.rup_sound cl_79354 [cl_70080,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70080 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_79370 : CNF.NClause := [(59,false),(29,true),(68,false),(70,false),(85,false),(44,false),(38,true),(12,false),(27,true),(72,false),(109,false),(75,false),(83,false),(81,false),(79,false),(119,false),(96,false),(64,false),(71,false)]
theorem der_79370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79370 :=
  CNF.rup_sound cl_79370 [cl_61255,cl_77322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61255 v h) (hints_cons _ _ _ (der_77322 v h) (by intro d hd; cases hd)))
def cl_79394 : CNF.NClause := [(102,false),(44,false),(19,false),(87,false),(115,false),(81,false),(103,false),(76,false),(68,false),(40,false),(137,false),(70,false),(79,false),(88,false),(142,true),(147,true),(69,false),(80,false),(85,false),(109,false)]
theorem der_79394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79394 :=
  CNF.rup_sound cl_79394 [cl_64888,cl_76536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64888 v h) (hints_cons _ _ _ (der_76536 v h) (by intro d hd; cases hd)))
def cl_79402 : CNF.NClause := [(39,false),(121,false),(74,false),(137,false),(66,false),(36,true),(110,false),(88,false),(6,false),(4,true),(70,false),(128,true),(54,true),(99,false),(91,false),(84,false),(65,false),(107,false),(134,true),(82,false),(135,true)]
theorem der_79402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79402 :=
  CNF.rup_sound cl_79402 [cl_58588,cl_66628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58588 v h) (hints_cons _ _ _ (der_66628 v h) (by intro d hd; cases hd)))
def cl_79405 : CNF.NClause := [(81,false),(68,false),(151,true),(63,false),(150,false),(65,false),(23,false),(95,false),(83,false),(42,true),(12,false),(70,false),(14,false),(85,false),(88,false),(74,false),(72,false),(52,false),(71,false),(152,true),(146,false)]
theorem der_79405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79405 :=
  CNF.rup_sound cl_79405 [cl_72620,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72620 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_79407 : CNF.NClause := [(151,false),(58,false),(137,true),(147,true),(125,true),(131,true),(47,false),(50,true),(140,false),(139,false),(144,true),(141,true),(130,true),(152,true),(132,true),(143,true),(83,false),(128,false),(73,false),(135,true),(146,false)]
theorem der_79407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79407 :=
  CNF.rup_sound cl_79407 [cl_75787,cl_75827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75787 v h) (hints_cons _ _ _ (der_75827 v h) (by intro d hd; cases hd)))
def cl_79409 : CNF.NClause := [(121,false),(39,false),(83,false),(6,false),(38,true),(66,false),(89,false),(41,true),(99,false),(63,false),(24,false),(81,false),(12,true),(110,false),(80,false),(34,true),(70,false),(65,false),(23,false),(84,false),(78,false),(76,false)]
theorem der_79409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79409 :=
  CNF.rup_sound cl_79409 [cl_53345,cl_60245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53345 v h) (hints_cons _ _ _ (der_60245 v h) (by intro d hd; cases hd)))
def cl_79414 : CNF.NClause := [(103,false),(76,false),(43,false),(4,false),(122,false),(65,false),(79,false),(42,true),(99,false),(139,true),(136,false),(133,true),(116,false),(70,false),(14,false),(83,false),(71,false),(74,false),(152,true),(95,false),(86,false),(67,false)]
theorem der_79414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79414 :=
  CNF.rup_sound cl_79414 [cl_69140,cl_42527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69140 v h) (hints_cons _ _ _ (der_42527 v h) (by intro d hd; cases hd)))
def cl_79421 : CNF.NClause := [(34,false),(118,false),(84,false),(74,false),(10,false),(96,false),(81,false),(131,false),(133,true),(83,false),(132,true),(73,false),(12,false),(85,false),(82,false),(92,false),(76,false),(101,false),(64,false),(86,false),(68,false),(75,false),(111,false)]
theorem der_79421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79421 :=
  CNF.rup_sound cl_79421 [cl_61978,cl_49832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61978 v h) (hints_cons _ _ _ (der_49832 v h) (by intro d hd; cases hd)))
def cl_79427 : CNF.NClause := [(12,true),(99,false),(17,true),(64,false),(36,true),(54,true),(85,false),(79,false),(119,false),(42,true),(86,false),(74,false),(90,false),(28,false),(75,false),(80,false),(60,false),(69,false),(67,false),(93,false),(65,false),(78,false),(3,false),(7,true)]
theorem der_79427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79427 :=
  CNF.rup_sound cl_79427 [cl_56549,cl_49686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56549 v h) (hints_cons _ _ _ (der_49686 v h) (by intro d hd; cases hd)))
def cl_79454 : CNF.NClause := [(70,true),(45,false),(14,true)]
theorem der_79454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79454 :=
  CNF.rup_sound cl_79454 [cl_77278,cl_77385,cl_51597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77278 v h) (hints_cons _ _ _ (der_77385 v h) (hints_cons _ _ _ (der_51597 v h) (by intro d hd; cases hd))))
def cl_79455 : CNF.NClause := [(79,false),(45,false),(14,true)]
theorem der_79455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79455 :=
  CNF.rup_sound cl_79455 [cl_49538,cl_77385,cl_77386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49538 v h) (hints_cons _ _ _ (der_77385 v h) (hints_cons _ _ _ (der_77386 v h) (by intro d hd; cases hd))))
def cl_79456 : CNF.NClause := [(72,false),(45,false),(14,true)]
theorem der_79456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79456 :=
  CNF.rup_sound cl_79456 [cl_79454,cl_79455,cl_78525,cl_77387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79454 v h) (hints_cons _ _ _ (der_79455 v h) (hints_cons _ _ _ (der_78525 v h) (hints_cons _ _ _ (der_77387 v h) (by intro d hd; cases hd)))))
def cl_79457 : CNF.NClause := [(45,false),(14,true)]
theorem der_79457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79457 :=
  CNF.rup_sound cl_79457 [cl_79454,cl_79455,cl_79456,cl_34831,cl_77369,cl_78403,cl_78478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79454 v h) (hints_cons _ _ _ (der_79455 v h) (hints_cons _ _ _ (der_79456 v h) (hints_cons _ _ _ (der_34831 v h) (hints_cons _ _ _ (der_77369 v h) (hints_cons _ _ _ (der_78403 v h) (hints_cons _ _ _ (der_78478 v h) (by intro d hd; cases hd))))))))
def cl_79458 : CNF.NClause := [(71,false),(44,false),(13,true)]
theorem der_79458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79458 :=
  CNF.rup_sound cl_79458 [cl_77310,cl_51671,cl_77318,cl_77372,cl_49673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77310 v h) (hints_cons _ _ _ (der_51671 v h) (hints_cons _ _ _ (der_77318 v h) (hints_cons _ _ _ (der_77372 v h) (hints_cons _ _ _ (der_49673 v h) (by intro d hd; cases hd))))))
def cl_79459 : CNF.NClause := [(90,false),(39,false),(8,true)]
theorem der_79459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79459 :=
  CNF.rup_sound cl_79459 [cl_77036,cl_56337,cl_77581,cl_77575,cl_77578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77036 v h) (hints_cons _ _ _ (der_56337 v h) (hints_cons _ _ _ (der_77581 v h) (hints_cons _ _ _ (der_77575 v h) (hints_cons _ _ _ (der_77578 v h) (by intro d hd; cases hd))))))
def cl_79460 : CNF.NClause := [(68,true),(47,false),(16,true)]
theorem der_79460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79460 :=
  CNF.rup_sound cl_79460 [cl_77287,cl_77025,cl_51646,cl_77293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77287 v h) (hints_cons _ _ _ (der_77025 v h) (hints_cons _ _ _ (der_51646 v h) (hints_cons _ _ _ (der_77293 v h) (by intro d hd; cases hd)))))
def cl_79461 : CNF.NClause := [(68,false),(43,false),(12,true)]
theorem der_79461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79461 :=
  CNF.rup_sound cl_79461 [cl_77109,cl_51060,cl_51078,cl_78079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77109 v h) (hints_cons _ _ _ (der_51060 v h) (hints_cons _ _ _ (der_51078 v h) (hints_cons _ _ _ (der_78079 v h) (by intro d hd; cases hd)))))
def cl_79462 : CNF.NClause := [(41,false),(75,false),(10,true)]
theorem der_79462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79462 :=
  CNF.rup_sound cl_79462 [cl_77155,cl_51247,cl_78194,cl_51254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77155 v h) (hints_cons _ _ _ (der_51247 v h) (hints_cons _ _ _ (der_78194 v h) (hints_cons _ _ _ (der_51254 v h) (by intro d hd; cases hd)))))
def cl_79463 : CNF.NClause := [(62,true),(71,false),(57,false)]
theorem der_79463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79463 :=
  CNF.rup_sound cl_79463 [cl_77184,cl_51321,cl_78261,cl_78272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77184 v h) (hints_cons _ _ _ (der_51321 v h) (hints_cons _ _ _ (der_78261 v h) (hints_cons _ _ _ (der_78272 v h) (by intro d hd; cases hd)))))
def cl_79466 : CNF.NClause := [(65,true),(86,false),(49,false)]
theorem der_79466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79466 :=
  CNF.rup_sound cl_79466 [cl_77330,cl_77373,cl_77376,cl_78451,cl_77481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77330 v h) (hints_cons _ _ _ (der_77373 v h) (hints_cons _ _ _ (der_77376 v h) (hints_cons _ _ _ (der_78451 v h) (hints_cons _ _ _ (der_77481 v h) (by intro d hd; cases hd))))))
def cl_79467 : CNF.NClause := [(71,false),(74,true),(50,false)]
theorem der_79467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79467 :=
  CNF.rup_sound cl_79467 [cl_77206,cl_51442,cl_77202,cl_51443,cl_51441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77206 v h) (hints_cons _ _ _ (der_51442 v h) (hints_cons _ _ _ (der_77202 v h) (hints_cons _ _ _ (der_51443 v h) (hints_cons _ _ _ (der_51441 v h) (by intro d hd; cases hd))))))
def cl_79469 : CNF.NClause := [(74,false),(71,true),(50,false)]
theorem der_79469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79469 :=
  CNF.rup_sound cl_79469 [cl_77205,cl_58854,cl_51457,cl_78329,cl_78343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77205 v h) (hints_cons _ _ _ (der_58854 v h) (hints_cons _ _ _ (der_51457 v h) (hints_cons _ _ _ (der_78329 v h) (hints_cons _ _ _ (der_78343 v h) (by intro d hd; cases hd))))))
def cl_79471 : CNF.NClause := [(66,false),(68,true),(47,false)]
theorem der_79471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79471 :=
  CNF.rup_sound cl_79471 [cl_79460,cl_77282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79460 v h) (hints_cons _ _ _ (der_77282 v h) (by intro d hd; cases hd)))
def cl_79472 : CNF.NClause := [(71,true),(84,false),(44,false)]
theorem der_79472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79472 :=
  CNF.rup_sound cl_79472 [cl_77359,cl_51775,cl_49673,cl_51790,cl_76655,cl_15787,cl_61981,cl_77242,cl_15767,cl_76597,cl_15786,cl_15773,cl_76588,cl_15785,cl_76591,cl_15791,cl_8025,cl_76552,cl_15794,cl_49767,cl_15783,cl_35284,cl_15775,cl_15662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77359 v h) (hints_cons _ _ _ (der_51775 v h) (hints_cons _ _ _ (der_49673 v h) (hints_cons _ _ _ (der_51790 v h) (hints_cons _ _ _ (der_76655 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_61981 v h) (hints_cons _ _ _ (der_77242 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_76597 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_76588 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_76591 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (inp_8025 v h) (hints_cons _ _ _ (der_76552 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_49767 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_35284 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_15662 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_79473 : CNF.NClause := [(84,true),(78,false),(44,false)]
theorem der_79473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79473 :=
  CNF.rup_sound cl_79473 [cl_57005,cl_77320,cl_49563,cl_49777,cl_15868,cl_76585,cl_15882,cl_76548,cl_15871,cl_49808,cl_15874,cl_76547,cl_15884,cl_49765,cl_15889,cl_49766,cl_15869,cl_15670,cl_43180,cl_15893,cl_49973,cl_15890,cl_12753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57005 v h) (hints_cons _ _ _ (der_77320 v h) (hints_cons _ _ _ (der_49563 v h) (hints_cons _ _ _ (der_49777 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_76585 v h) (hints_cons _ _ _ (der_15882 v h) (hints_cons _ _ _ (der_76548 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_49808 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_76547 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_49765 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_49766 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_15670 v h) (hints_cons _ _ _ (der_43180 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_49973 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (inp_12753 v h) (by intro d hd; cases hd))))))))))))))))))))))))
def cl_79474 : CNF.NClause := [(84,true),(88,false),(44,false)]
theorem der_79474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79474 :=
  CNF.rup_sound cl_79474 [cl_77365,cl_79473,cl_51695,cl_51581,cl_78465,cl_78468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77365 v h) (hints_cons _ _ _ (der_79473 v h) (hints_cons _ _ _ (der_51695 v h) (hints_cons _ _ _ (der_51581 v h) (hints_cons _ _ _ (der_78465 v h) (hints_cons _ _ _ (der_78468 v h) (by intro d hd; cases hd)))))))
def cl_79475 : CNF.NClause := [(75,true),(88,false),(40,false)]
theorem der_79475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79475 :=
  CNF.rup_sound cl_79475 [cl_77073,cl_77077,cl_77780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77073 v h) (hints_cons _ _ _ (der_77077 v h) (hints_cons _ _ _ (der_77780 v h) (by intro d hd; cases hd))))
def chunk077 : List CNF.NClause := [cl_78343,cl_78345,cl_78346,cl_78348,cl_78349,cl_78351,cl_78357,cl_78358,cl_78363,cl_78364,cl_78366,cl_78367,cl_78370,cl_78372,cl_78373,cl_78374,cl_78375,cl_78376,cl_78380,cl_78381,cl_78383,cl_78384,cl_78385,cl_78386,cl_78388,cl_78389,cl_78393,cl_78396,cl_78401,cl_78402,cl_78403,cl_78405,cl_78408,cl_78409,cl_78410,cl_78412,cl_78416,cl_78418,cl_78419,cl_78420,cl_78421,cl_78422,cl_78424,cl_78426,cl_78427,cl_78429,cl_78430,cl_78431,cl_78432,cl_78433,cl_78435,cl_78447,cl_78449,cl_78450,cl_78451,cl_78454,cl_78455,cl_78457,cl_78459,cl_78460,cl_78461,cl_78462,cl_78463,cl_78464,cl_78465,cl_78467,cl_78468,cl_78469,cl_78470,cl_78472,cl_78474,cl_78477,cl_78478,cl_78479,cl_78480,cl_78482,cl_78483,cl_78485,cl_78487,cl_78491,cl_78493,cl_78494,cl_78496,cl_78497,cl_78499,cl_78500,cl_78503,cl_78504,cl_78505,cl_78506,cl_78508,cl_78510,cl_78511,cl_78513,cl_78515,cl_78518,cl_78521,cl_78522,cl_78523,cl_78524,cl_78525,cl_78526,cl_78527,cl_78530,cl_78532,cl_78533,cl_78535,cl_78536,cl_78542,cl_78543,cl_78544,cl_78545,cl_78546,cl_78550,cl_78551,cl_78553,cl_78554,cl_78555,cl_78562,cl_78563,cl_78571,cl_78573,cl_78577,cl_78579,cl_78580,cl_78583,cl_78584,cl_78585,cl_78587,cl_78588,cl_78589,cl_78590,cl_78591,cl_78592,cl_78593,cl_78595,cl_78596,cl_78597,cl_78598,cl_78601,cl_78603,cl_78604,cl_78606,cl_78608,cl_78610,cl_78612,cl_78613,cl_78617,cl_78619,cl_78620,cl_78621,cl_78622,cl_78624,cl_78626,cl_78627,cl_78629,cl_78631,cl_78632,cl_78633,cl_78634,cl_78635,cl_78636,cl_78637,cl_78639,cl_78640,cl_78641,cl_78642,cl_78643,cl_78644,cl_78645,cl_78646,cl_78647,cl_78648,cl_78649,cl_78650,cl_78651,cl_78652,cl_78653,cl_78655,cl_78656,cl_78657,cl_78659,cl_78660,cl_78661,cl_78663,cl_78664,cl_78665,cl_78666,cl_78667,cl_78668,cl_78669,cl_78670,cl_78671,cl_78672,cl_78673,cl_78675,cl_78676,cl_78677,cl_78678,cl_78679,cl_78681,cl_78686,cl_78687,cl_78688,cl_78689,cl_78690,cl_78691,cl_78692,cl_78693,cl_78695,cl_78696,cl_78697,cl_78698,cl_78699,cl_78700,cl_78701,cl_78702,cl_78703,cl_78705,cl_78706,cl_78709,cl_78715,cl_78719,cl_78720,cl_78722,cl_78724,cl_78725,cl_78726,cl_78728,cl_78729,cl_78731,cl_78733,cl_78734,cl_78735,cl_78736,cl_78739,cl_78740,cl_78741,cl_78742,cl_78743,cl_78744,cl_78745,cl_78746,cl_78747,cl_78749,cl_78751,cl_78752,cl_78753,cl_78756,cl_78758,cl_78760,cl_78762,cl_78763,cl_78765,cl_78766,cl_78767,cl_78768,cl_78769,cl_78771,cl_78772,cl_78774,cl_78775,cl_78776,cl_78779,cl_78780,cl_78781,cl_78782,cl_78785,cl_78788,cl_78789,cl_78790,cl_78792,cl_78796,cl_78797,cl_78799,cl_78800,cl_78802,cl_78803,cl_78804,cl_78806,cl_78807,cl_78809,cl_78813,cl_78814,cl_78815,cl_78816,cl_78820,cl_78822,cl_78824,cl_78826,cl_78827,cl_78828,cl_78829,cl_78830,cl_78831,cl_78833,cl_78834,cl_78836,cl_78838,cl_78839,cl_78841,cl_78847,cl_78848,cl_78849,cl_78850,cl_78861,cl_78862,cl_78864,cl_78868,cl_78873,cl_78874,cl_78881,cl_78883,cl_78884,cl_78887,cl_78888,cl_78890,cl_78892,cl_78897,cl_78899,cl_78901,cl_78903,cl_78904,cl_78905,cl_78906,cl_78908,cl_78909,cl_78913,cl_78914,cl_78915,cl_78918,cl_78925,cl_78927,cl_78929,cl_78944,cl_78952,cl_78955,cl_78956,cl_78957,cl_78958,cl_78965,cl_78967,cl_78968,cl_78972,cl_78980,cl_78993,cl_79017,cl_79028,cl_79033,cl_79041,cl_79042,cl_79047,cl_79049,cl_79050,cl_79051,cl_79052,cl_79067,cl_79079,cl_79080,cl_79081,cl_79082,cl_79086,cl_79087,cl_79088,cl_79092,cl_79094,cl_79097,cl_79098,cl_79103,cl_79116,cl_79118,cl_79120,cl_79121,cl_79122,cl_79125,cl_79126,cl_79127,cl_79128,cl_79130,cl_79131,cl_79133,cl_79134,cl_79136,cl_79138,cl_79145,cl_79150,cl_79154,cl_79156,cl_79157,cl_79159,cl_79160,cl_79161,cl_79162,cl_79165,cl_79166,cl_79167,cl_79169,cl_79170,cl_79171,cl_79173,cl_79176,cl_79178,cl_79180,cl_79181,cl_79184,cl_79192,cl_79193,cl_79197,cl_79199,cl_79202,cl_79203,cl_79204,cl_79205,cl_79212,cl_79213,cl_79215,cl_79218,cl_79219,cl_79220,cl_79221,cl_79222,cl_79224,cl_79225,cl_79226,cl_79228,cl_79229,cl_79230,cl_79231,cl_79232,cl_79233,cl_79234,cl_79235,cl_79237,cl_79238,cl_79239,cl_79248,cl_79251,cl_79252,cl_79254,cl_79255,cl_79256,cl_79257,cl_79262,cl_79265,cl_79266,cl_79267,cl_79279,cl_79280,cl_79284,cl_79287,cl_79288,cl_79289,cl_79290,cl_79291,cl_79300,cl_79302,cl_79303,cl_79304,cl_79309,cl_79310,cl_79312,cl_79314,cl_79315,cl_79322,cl_79323,cl_79327,cl_79330,cl_79335,cl_79338,cl_79341,cl_79346,cl_79350,cl_79354,cl_79370,cl_79394,cl_79402,cl_79405,cl_79407,cl_79409,cl_79414,cl_79421,cl_79427,cl_79454,cl_79455,cl_79456,cl_79457,cl_79458,cl_79459,cl_79460,cl_79461,cl_79462,cl_79463,cl_79466,cl_79467,cl_79469,cl_79471,cl_79472,cl_79473,cl_79474,cl_79475]
theorem chunk_sound077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk077, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_78343 v h) (hints_cons _ _ _ (der_78345 v h) (hints_cons _ _ _ (der_78346 v h) (hints_cons _ _ _ (der_78348 v h) (hints_cons _ _ _ (der_78349 v h) (hints_cons _ _ _ (der_78351 v h) (hints_cons _ _ _ (der_78357 v h) (hints_cons _ _ _ (der_78358 v h) (hints_cons _ _ _ (der_78363 v h) (hints_cons _ _ _ (der_78364 v h) (hints_cons _ _ _ (der_78366 v h) (hints_cons _ _ _ (der_78367 v h) (hints_cons _ _ _ (der_78370 v h) (hints_cons _ _ _ (der_78372 v h) (hints_cons _ _ _ (der_78373 v h) (hints_cons _ _ _ (der_78374 v h) (hints_cons _ _ _ (der_78375 v h) (hints_cons _ _ _ (der_78376 v h) (hints_cons _ _ _ (der_78380 v h) (hints_cons _ _ _ (der_78381 v h) (hints_cons _ _ _ (der_78383 v h) (hints_cons _ _ _ (der_78384 v h) (hints_cons _ _ _ (der_78385 v h) (hints_cons _ _ _ (der_78386 v h) (hints_cons _ _ _ (der_78388 v h) (hints_cons _ _ _ (der_78389 v h) (hints_cons _ _ _ (der_78393 v h) (hints_cons _ _ _ (der_78396 v h) (hints_cons _ _ _ (der_78401 v h) (hints_cons _ _ _ (der_78402 v h) (hints_cons _ _ _ (der_78403 v h) (hints_cons _ _ _ (der_78405 v h) (hints_cons _ _ _ (der_78408 v h) (hints_cons _ _ _ (der_78409 v h) (hints_cons _ _ _ (der_78410 v h) (hints_cons _ _ _ (der_78412 v h) (hints_cons _ _ _ (der_78416 v h) (hints_cons _ _ _ (der_78418 v h) (hints_cons _ _ _ (der_78419 v h) (hints_cons _ _ _ (der_78420 v h) (hints_cons _ _ _ (der_78421 v h) (hints_cons _ _ _ (der_78422 v h) (hints_cons _ _ _ (der_78424 v h) (hints_cons _ _ _ (der_78426 v h) (hints_cons _ _ _ (der_78427 v h) (hints_cons _ _ _ (der_78429 v h) (hints_cons _ _ _ (der_78430 v h) (hints_cons _ _ _ (der_78431 v h) (hints_cons _ _ _ (der_78432 v h) (hints_cons _ _ _ (der_78433 v h) (hints_cons _ _ _ (der_78435 v h) (hints_cons _ _ _ (der_78447 v h) (hints_cons _ _ _ (der_78449 v h) (hints_cons _ _ _ (der_78450 v h) (hints_cons _ _ _ (der_78451 v h) (hints_cons _ _ _ (der_78454 v h) (hints_cons _ _ _ (der_78455 v h) (hints_cons _ _ _ (der_78457 v h) (hints_cons _ _ _ (der_78459 v h) (hints_cons _ _ _ (der_78460 v h) (hints_cons _ _ _ (der_78461 v h) (hints_cons _ _ _ (der_78462 v h) (hints_cons _ _ _ (der_78463 v h) (hints_cons _ _ _ (der_78464 v h) (hints_cons _ _ _ (der_78465 v h) (hints_cons _ _ _ (der_78467 v h) (hints_cons _ _ _ (der_78468 v h) (hints_cons _ _ _ (der_78469 v h) (hints_cons _ _ _ (der_78470 v h) (hints_cons _ _ _ (der_78472 v h) (hints_cons _ _ _ (der_78474 v h) (hints_cons _ _ _ (der_78477 v h) (hints_cons _ _ _ (der_78478 v h) (hints_cons _ _ _ (der_78479 v h) (hints_cons _ _ _ (der_78480 v h) (hints_cons _ _ _ (der_78482 v h) (hints_cons _ _ _ (der_78483 v h) (hints_cons _ _ _ (der_78485 v h) (hints_cons _ _ _ (der_78487 v h) (hints_cons _ _ _ (der_78491 v h) (hints_cons _ _ _ (der_78493 v h) (hints_cons _ _ _ (der_78494 v h) (hints_cons _ _ _ (der_78496 v h) (hints_cons _ _ _ (der_78497 v h) (hints_cons _ _ _ (der_78499 v h) (hints_cons _ _ _ (der_78500 v h) (hints_cons _ _ _ (der_78503 v h) (hints_cons _ _ _ (der_78504 v h) (hints_cons _ _ _ (der_78505 v h) (hints_cons _ _ _ (der_78506 v h) (hints_cons _ _ _ (der_78508 v h) (hints_cons _ _ _ (der_78510 v h) (hints_cons _ _ _ (der_78511 v h) (hints_cons _ _ _ (der_78513 v h) (hints_cons _ _ _ (der_78515 v h) (hints_cons _ _ _ (der_78518 v h) (hints_cons _ _ _ (der_78521 v h) (hints_cons _ _ _ (der_78522 v h) (hints_cons _ _ _ (der_78523 v h) (hints_cons _ _ _ (der_78524 v h) (hints_cons _ _ _ (der_78525 v h) (hints_cons _ _ _ (der_78526 v h) (hints_cons _ _ _ (der_78527 v h) (hints_cons _ _ _ (der_78530 v h) (hints_cons _ _ _ (der_78532 v h) (hints_cons _ _ _ (der_78533 v h) (hints_cons _ _ _ (der_78535 v h) (hints_cons _ _ _ (der_78536 v h) (hints_cons _ _ _ (der_78542 v h) (hints_cons _ _ _ (der_78543 v h) (hints_cons _ _ _ (der_78544 v h) (hints_cons _ _ _ (der_78545 v h) (hints_cons _ _ _ (der_78546 v h) (hints_cons _ _ _ (der_78550 v h) (hints_cons _ _ _ (der_78551 v h) (hints_cons _ _ _ (der_78553 v h) (hints_cons _ _ _ (der_78554 v h) (hints_cons _ _ _ (der_78555 v h) (hints_cons _ _ _ (der_78562 v h) (hints_cons _ _ _ (der_78563 v h) (hints_cons _ _ _ (der_78571 v h) (hints_cons _ _ _ (der_78573 v h) (hints_cons _ _ _ (der_78577 v h) (hints_cons _ _ _ (der_78579 v h) (hints_cons _ _ _ (der_78580 v h) (hints_cons _ _ _ (der_78583 v h) (hints_cons _ _ _ (der_78584 v h) (hints_cons _ _ _ (der_78585 v h) (hints_cons _ _ _ (der_78587 v h) (hints_cons _ _ _ (der_78588 v h) (hints_cons _ _ _ (der_78589 v h) (hints_cons _ _ _ (der_78590 v h) (hints_cons _ _ _ (der_78591 v h) (hints_cons _ _ _ (der_78592 v h) (hints_cons _ _ _ (der_78593 v h) (hints_cons _ _ _ (der_78595 v h) (hints_cons _ _ _ (der_78596 v h) (hints_cons _ _ _ (der_78597 v h) (hints_cons _ _ _ (der_78598 v h) (hints_cons _ _ _ (der_78601 v h) (hints_cons _ _ _ (der_78603 v h) (hints_cons _ _ _ (der_78604 v h) (hints_cons _ _ _ (der_78606 v h) (hints_cons _ _ _ (der_78608 v h) (hints_cons _ _ _ (der_78610 v h) (hints_cons _ _ _ (der_78612 v h) (hints_cons _ _ _ (der_78613 v h) (hints_cons _ _ _ (der_78617 v h) (hints_cons _ _ _ (der_78619 v h) (hints_cons _ _ _ (der_78620 v h) (hints_cons _ _ _ (der_78621 v h) (hints_cons _ _ _ (der_78622 v h) (hints_cons _ _ _ (der_78624 v h) (hints_cons _ _ _ (der_78626 v h) (hints_cons _ _ _ (der_78627 v h) (hints_cons _ _ _ (der_78629 v h) (hints_cons _ _ _ (der_78631 v h) (hints_cons _ _ _ (der_78632 v h) (hints_cons _ _ _ (der_78633 v h) (hints_cons _ _ _ (der_78634 v h) (hints_cons _ _ _ (der_78635 v h) (hints_cons _ _ _ (der_78636 v h) (hints_cons _ _ _ (der_78637 v h) (hints_cons _ _ _ (der_78639 v h) (hints_cons _ _ _ (der_78640 v h) (hints_cons _ _ _ (der_78641 v h) (hints_cons _ _ _ (der_78642 v h) (hints_cons _ _ _ (der_78643 v h) (hints_cons _ _ _ (der_78644 v h) (hints_cons _ _ _ (der_78645 v h) (hints_cons _ _ _ (der_78646 v h) (hints_cons _ _ _ (der_78647 v h) (hints_cons _ _ _ (der_78648 v h) (hints_cons _ _ _ (der_78649 v h) (hints_cons _ _ _ (der_78650 v h) (hints_cons _ _ _ (der_78651 v h) (hints_cons _ _ _ (der_78652 v h) (hints_cons _ _ _ (der_78653 v h) (hints_cons _ _ _ (der_78655 v h) (hints_cons _ _ _ (der_78656 v h) (hints_cons _ _ _ (der_78657 v h) (hints_cons _ _ _ (der_78659 v h) (hints_cons _ _ _ (der_78660 v h) (hints_cons _ _ _ (der_78661 v h) (hints_cons _ _ _ (der_78663 v h) (hints_cons _ _ _ (der_78664 v h) (hints_cons _ _ _ (der_78665 v h) (hints_cons _ _ _ (der_78666 v h) (hints_cons _ _ _ (der_78667 v h) (hints_cons _ _ _ (der_78668 v h) (hints_cons _ _ _ (der_78669 v h) (hints_cons _ _ _ (der_78670 v h) (hints_cons _ _ _ (der_78671 v h) (hints_cons _ _ _ (der_78672 v h) (hints_cons _ _ _ (der_78673 v h) (hints_cons _ _ _ (der_78675 v h) (hints_cons _ _ _ (der_78676 v h) (hints_cons _ _ _ (der_78677 v h) (hints_cons _ _ _ (der_78678 v h) (hints_cons _ _ _ (der_78679 v h) (hints_cons _ _ _ (der_78681 v h) (hints_cons _ _ _ (der_78686 v h) (hints_cons _ _ _ (der_78687 v h) (hints_cons _ _ _ (der_78688 v h) (hints_cons _ _ _ (der_78689 v h) (hints_cons _ _ _ (der_78690 v h) (hints_cons _ _ _ (der_78691 v h) (hints_cons _ _ _ (der_78692 v h) (hints_cons _ _ _ (der_78693 v h) (hints_cons _ _ _ (der_78695 v h) (hints_cons _ _ _ (der_78696 v h) (hints_cons _ _ _ (der_78697 v h) (hints_cons _ _ _ (der_78698 v h) (hints_cons _ _ _ (der_78699 v h) (hints_cons _ _ _ (der_78700 v h) (hints_cons _ _ _ (der_78701 v h) (hints_cons _ _ _ (der_78702 v h) (hints_cons _ _ _ (der_78703 v h) (hints_cons _ _ _ (der_78705 v h) (hints_cons _ _ _ (der_78706 v h) (hints_cons _ _ _ (der_78709 v h) (hints_cons _ _ _ (der_78715 v h) (hints_cons _ _ _ (der_78719 v h) (hints_cons _ _ _ (der_78720 v h) (hints_cons _ _ _ (der_78722 v h) (hints_cons _ _ _ (der_78724 v h) (hints_cons _ _ _ (der_78725 v h) (hints_cons _ _ _ (der_78726 v h) (hints_cons _ _ _ (der_78728 v h) (hints_cons _ _ _ (der_78729 v h) (hints_cons _ _ _ (der_78731 v h) (hints_cons _ _ _ (der_78733 v h) (hints_cons _ _ _ (der_78734 v h) (hints_cons _ _ _ (der_78735 v h) (hints_cons _ _ _ (der_78736 v h) (hints_cons _ _ _ (der_78739 v h) (hints_cons _ _ _ (der_78740 v h) (hints_cons _ _ _ (der_78741 v h) (hints_cons _ _ _ (der_78742 v h) (hints_cons _ _ _ (der_78743 v h) (hints_cons _ _ _ (der_78744 v h) (hints_cons _ _ _ (der_78745 v h) (hints_cons _ _ _ (der_78746 v h) (hints_cons _ _ _ (der_78747 v h) (hints_cons _ _ _ (der_78749 v h) (hints_cons _ _ _ (der_78751 v h) (hints_cons _ _ _ (der_78752 v h) (hints_cons _ _ _ (der_78753 v h) (hints_cons _ _ _ (der_78756 v h) (hints_cons _ _ _ (der_78758 v h) (hints_cons _ _ _ (der_78760 v h) (hints_cons _ _ _ (der_78762 v h) (hints_cons _ _ _ (der_78763 v h) (hints_cons _ _ _ (der_78765 v h) (hints_cons _ _ _ (der_78766 v h) (hints_cons _ _ _ (der_78767 v h) (hints_cons _ _ _ (der_78768 v h) (hints_cons _ _ _ (der_78769 v h) (hints_cons _ _ _ (der_78771 v h) (hints_cons _ _ _ (der_78772 v h) (hints_cons _ _ _ (der_78774 v h) (hints_cons _ _ _ (der_78775 v h) (hints_cons _ _ _ (der_78776 v h) (hints_cons _ _ _ (der_78779 v h) (hints_cons _ _ _ (der_78780 v h) (hints_cons _ _ _ (der_78781 v h) (hints_cons _ _ _ (der_78782 v h) (hints_cons _ _ _ (der_78785 v h) (hints_cons _ _ _ (der_78788 v h) (hints_cons _ _ _ (der_78789 v h) (hints_cons _ _ _ (der_78790 v h) (hints_cons _ _ _ (der_78792 v h) (hints_cons _ _ _ (der_78796 v h) (hints_cons _ _ _ (der_78797 v h) (hints_cons _ _ _ (der_78799 v h) (hints_cons _ _ _ (der_78800 v h) (hints_cons _ _ _ (der_78802 v h) (hints_cons _ _ _ (der_78803 v h) (hints_cons _ _ _ (der_78804 v h) (hints_cons _ _ _ (der_78806 v h) (hints_cons _ _ _ (der_78807 v h) (hints_cons _ _ _ (der_78809 v h) (hints_cons _ _ _ (der_78813 v h) (hints_cons _ _ _ (der_78814 v h) (hints_cons _ _ _ (der_78815 v h) (hints_cons _ _ _ (der_78816 v h) (hints_cons _ _ _ (der_78820 v h) (hints_cons _ _ _ (der_78822 v h) (hints_cons _ _ _ (der_78824 v h) (hints_cons _ _ _ (der_78826 v h) (hints_cons _ _ _ (der_78827 v h) (hints_cons _ _ _ (der_78828 v h) (hints_cons _ _ _ (der_78829 v h) (hints_cons _ _ _ (der_78830 v h) (hints_cons _ _ _ (der_78831 v h) (hints_cons _ _ _ (der_78833 v h) (hints_cons _ _ _ (der_78834 v h) (hints_cons _ _ _ (der_78836 v h) (hints_cons _ _ _ (der_78838 v h) (hints_cons _ _ _ (der_78839 v h) (hints_cons _ _ _ (der_78841 v h) (hints_cons _ _ _ (der_78847 v h) (hints_cons _ _ _ (der_78848 v h) (hints_cons _ _ _ (der_78849 v h) (hints_cons _ _ _ (der_78850 v h) (hints_cons _ _ _ (der_78861 v h) (hints_cons _ _ _ (der_78862 v h) (hints_cons _ _ _ (der_78864 v h) (hints_cons _ _ _ (der_78868 v h) (hints_cons _ _ _ (der_78873 v h) (hints_cons _ _ _ (der_78874 v h) (hints_cons _ _ _ (der_78881 v h) (hints_cons _ _ _ (der_78883 v h) (hints_cons _ _ _ (der_78884 v h) (hints_cons _ _ _ (der_78887 v h) (hints_cons _ _ _ (der_78888 v h) (hints_cons _ _ _ (der_78890 v h) (hints_cons _ _ _ (der_78892 v h) (hints_cons _ _ _ (der_78897 v h) (hints_cons _ _ _ (der_78899 v h) (hints_cons _ _ _ (der_78901 v h) (hints_cons _ _ _ (der_78903 v h) (hints_cons _ _ _ (der_78904 v h) (hints_cons _ _ _ (der_78905 v h) (hints_cons _ _ _ (der_78906 v h) (hints_cons _ _ _ (der_78908 v h) (hints_cons _ _ _ (der_78909 v h) (hints_cons _ _ _ (der_78913 v h) (hints_cons _ _ _ (der_78914 v h) (hints_cons _ _ _ (der_78915 v h) (hints_cons _ _ _ (der_78918 v h) (hints_cons _ _ _ (der_78925 v h) (hints_cons _ _ _ (der_78927 v h) (hints_cons _ _ _ (der_78929 v h) (hints_cons _ _ _ (der_78944 v h) (hints_cons _ _ _ (der_78952 v h) (hints_cons _ _ _ (der_78955 v h) (hints_cons _ _ _ (der_78956 v h) (hints_cons _ _ _ (der_78957 v h) (hints_cons _ _ _ (der_78958 v h) (hints_cons _ _ _ (der_78965 v h) (hints_cons _ _ _ (der_78967 v h) (hints_cons _ _ _ (der_78968 v h) (hints_cons _ _ _ (der_78972 v h) (hints_cons _ _ _ (der_78980 v h) (hints_cons _ _ _ (der_78993 v h) (hints_cons _ _ _ (der_79017 v h) (hints_cons _ _ _ (der_79028 v h) (hints_cons _ _ _ (der_79033 v h) (hints_cons _ _ _ (der_79041 v h) (hints_cons _ _ _ (der_79042 v h) (hints_cons _ _ _ (der_79047 v h) (hints_cons _ _ _ (der_79049 v h) (hints_cons _ _ _ (der_79050 v h) (hints_cons _ _ _ (der_79051 v h) (hints_cons _ _ _ (der_79052 v h) (hints_cons _ _ _ (der_79067 v h) (hints_cons _ _ _ (der_79079 v h) (hints_cons _ _ _ (der_79080 v h) (hints_cons _ _ _ (der_79081 v h) (hints_cons _ _ _ (der_79082 v h) (hints_cons _ _ _ (der_79086 v h) (hints_cons _ _ _ (der_79087 v h) (hints_cons _ _ _ (der_79088 v h) (hints_cons _ _ _ (der_79092 v h) (hints_cons _ _ _ (der_79094 v h) (hints_cons _ _ _ (der_79097 v h) (hints_cons _ _ _ (der_79098 v h) (hints_cons _ _ _ (der_79103 v h) (hints_cons _ _ _ (der_79116 v h) (hints_cons _ _ _ (der_79118 v h) (hints_cons _ _ _ (der_79120 v h) (hints_cons _ _ _ (der_79121 v h) (hints_cons _ _ _ (der_79122 v h) (hints_cons _ _ _ (der_79125 v h) (hints_cons _ _ _ (der_79126 v h) (hints_cons _ _ _ (der_79127 v h) (hints_cons _ _ _ (der_79128 v h) (hints_cons _ _ _ (der_79130 v h) (hints_cons _ _ _ (der_79131 v h) (hints_cons _ _ _ (der_79133 v h) (hints_cons _ _ _ (der_79134 v h) (hints_cons _ _ _ (der_79136 v h) (hints_cons _ _ _ (der_79138 v h) (hints_cons _ _ _ (der_79145 v h) (hints_cons _ _ _ (der_79150 v h) (hints_cons _ _ _ (der_79154 v h) (hints_cons _ _ _ (der_79156 v h) (hints_cons _ _ _ (der_79157 v h) (hints_cons _ _ _ (der_79159 v h) (hints_cons _ _ _ (der_79160 v h) (hints_cons _ _ _ (der_79161 v h) (hints_cons _ _ _ (der_79162 v h) (hints_cons _ _ _ (der_79165 v h) (hints_cons _ _ _ (der_79166 v h) (hints_cons _ _ _ (der_79167 v h) (hints_cons _ _ _ (der_79169 v h) (hints_cons _ _ _ (der_79170 v h) (hints_cons _ _ _ (der_79171 v h) (hints_cons _ _ _ (der_79173 v h) (hints_cons _ _ _ (der_79176 v h) (hints_cons _ _ _ (der_79178 v h) (hints_cons _ _ _ (der_79180 v h) (hints_cons _ _ _ (der_79181 v h) (hints_cons _ _ _ (der_79184 v h) (hints_cons _ _ _ (der_79192 v h) (hints_cons _ _ _ (der_79193 v h) (hints_cons _ _ _ (der_79197 v h) (hints_cons _ _ _ (der_79199 v h) (hints_cons _ _ _ (der_79202 v h) (hints_cons _ _ _ (der_79203 v h) (hints_cons _ _ _ (der_79204 v h) (hints_cons _ _ _ (der_79205 v h) (hints_cons _ _ _ (der_79212 v h) (hints_cons _ _ _ (der_79213 v h) (hints_cons _ _ _ (der_79215 v h) (hints_cons _ _ _ (der_79218 v h) (hints_cons _ _ _ (der_79219 v h) (hints_cons _ _ _ (der_79220 v h) (hints_cons _ _ _ (der_79221 v h) (hints_cons _ _ _ (der_79222 v h) (hints_cons _ _ _ (der_79224 v h) (hints_cons _ _ _ (der_79225 v h) (hints_cons _ _ _ (der_79226 v h) (hints_cons _ _ _ (der_79228 v h) (hints_cons _ _ _ (der_79229 v h) (hints_cons _ _ _ (der_79230 v h) (hints_cons _ _ _ (der_79231 v h) (hints_cons _ _ _ (der_79232 v h) (hints_cons _ _ _ (der_79233 v h) (hints_cons _ _ _ (der_79234 v h) (hints_cons _ _ _ (der_79235 v h) (hints_cons _ _ _ (der_79237 v h) (hints_cons _ _ _ (der_79238 v h) (hints_cons _ _ _ (der_79239 v h) (hints_cons _ _ _ (der_79248 v h) (hints_cons _ _ _ (der_79251 v h) (hints_cons _ _ _ (der_79252 v h) (hints_cons _ _ _ (der_79254 v h) (hints_cons _ _ _ (der_79255 v h) (hints_cons _ _ _ (der_79256 v h) (hints_cons _ _ _ (der_79257 v h) (hints_cons _ _ _ (der_79262 v h) (hints_cons _ _ _ (der_79265 v h) (hints_cons _ _ _ (der_79266 v h) (hints_cons _ _ _ (der_79267 v h) (hints_cons _ _ _ (der_79279 v h) (hints_cons _ _ _ (der_79280 v h) (hints_cons _ _ _ (der_79284 v h) (hints_cons _ _ _ (der_79287 v h) (hints_cons _ _ _ (der_79288 v h) (hints_cons _ _ _ (der_79289 v h) (hints_cons _ _ _ (der_79290 v h) (hints_cons _ _ _ (der_79291 v h) (hints_cons _ _ _ (der_79300 v h) (hints_cons _ _ _ (der_79302 v h) (hints_cons _ _ _ (der_79303 v h) (hints_cons _ _ _ (der_79304 v h) (hints_cons _ _ _ (der_79309 v h) (hints_cons _ _ _ (der_79310 v h) (hints_cons _ _ _ (der_79312 v h) (hints_cons _ _ _ (der_79314 v h) (hints_cons _ _ _ (der_79315 v h) (hints_cons _ _ _ (der_79322 v h) (hints_cons _ _ _ (der_79323 v h) (hints_cons _ _ _ (der_79327 v h) (hints_cons _ _ _ (der_79330 v h) (hints_cons _ _ _ (der_79335 v h) (hints_cons _ _ _ (der_79338 v h) (hints_cons _ _ _ (der_79341 v h) (hints_cons _ _ _ (der_79346 v h) (hints_cons _ _ _ (der_79350 v h) (hints_cons _ _ _ (der_79354 v h) (hints_cons _ _ _ (der_79370 v h) (hints_cons _ _ _ (der_79394 v h) (hints_cons _ _ _ (der_79402 v h) (hints_cons _ _ _ (der_79405 v h) (hints_cons _ _ _ (der_79407 v h) (hints_cons _ _ _ (der_79409 v h) (hints_cons _ _ _ (der_79414 v h) (hints_cons _ _ _ (der_79421 v h) (hints_cons _ _ _ (der_79427 v h) (hints_cons _ _ _ (der_79454 v h) (hints_cons _ _ _ (der_79455 v h) (hints_cons _ _ _ (der_79456 v h) (hints_cons _ _ _ (der_79457 v h) (hints_cons _ _ _ (der_79458 v h) (hints_cons _ _ _ (der_79459 v h) (hints_cons _ _ _ (der_79460 v h) (hints_cons _ _ _ (der_79461 v h) (hints_cons _ _ _ (der_79462 v h) (hints_cons _ _ _ (der_79463 v h) (hints_cons _ _ _ (der_79466 v h) (hints_cons _ _ _ (der_79467 v h) (hints_cons _ _ _ (der_79469 v h) (hints_cons _ _ _ (der_79471 v h) (hints_cons _ _ _ (der_79472 v h) (hints_cons _ _ _ (der_79473 v h) (hints_cons _ _ _ (der_79474 v h) (hints_cons _ _ _ (der_79475 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix077 := prefix076 ++ chunk077
theorem prefix_sound077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix077, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound076 v h c hc
  · exact chunk_sound077 v h c hc
end Percolation.NReplay
