import NReplay013
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_29370 : CNF.NClause := [(49,false),(69,true),(65,true),(73,true),(77,true),(86,true),(91,true)]
theorem der_29370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29370 :=
  CNF.rup_sound cl_29370 [cl_6400,cl_29306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6400 v h) (hints_cons _ _ _ (der_29306 v h) (by intro d hd; cases hd)))
def cl_29371 : CNF.NClause := [(49,false),(86,false),(18,false),(69,false),(77,false),(73,true),(91,false)]
theorem der_29371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29371 :=
  CNF.rup_sound cl_29371 [cl_6281,cl_29277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6281 v h) (hints_cons _ _ _ (der_29277 v h) (by intro d hd; cases hd)))
def cl_29372 : CNF.NClause := [(49,false),(77,true),(18,false),(69,false),(73,true),(86,false),(91,false)]
theorem der_29372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29372 :=
  CNF.rup_sound cl_29372 [cl_6297,cl_29345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6297 v h) (hints_cons _ _ _ (der_29345 v h) (by intro d hd; cases hd)))
def cl_29373 : CNF.NClause := [(49,false),(18,false),(69,false),(65,false),(77,false),(86,true),(91,false)]
theorem der_29373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29373 :=
  CNF.rup_sound cl_29373 [cl_6313,cl_6305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6313 v h) (hints_cons _ _ _ (inp_6305 v h) (by intro d hd; cases hd)))
def cl_29374 : CNF.NClause := [(49,false),(77,true),(18,false),(69,false),(65,false),(86,true),(91,false)]
theorem der_29374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29374 :=
  CNF.rup_sound cl_29374 [cl_6329,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6329 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_29375 : CNF.NClause := [(49,false),(86,false),(18,false),(69,false),(65,false),(77,false),(91,true)]
theorem der_29375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29375 :=
  CNF.rup_sound cl_29375 [cl_6345,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6345 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29376 : CNF.NClause := [(49,false),(77,true),(18,false),(69,false),(73,true),(86,false),(91,true)]
theorem der_29376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29376 :=
  CNF.rup_sound cl_29376 [cl_6361,cl_29297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6361 v h) (hints_cons _ _ _ (der_29297 v h) (by intro d hd; cases hd)))
def cl_29377 : CNF.NClause := [(49,false),(91,true),(18,false),(69,false),(65,false),(86,true),(77,false)]
theorem der_29377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29377 :=
  CNF.rup_sound cl_29377 [cl_6377,cl_29041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6377 v h) (hints_cons _ _ _ (der_29041 v h) (by intro d hd; cases hd)))
def cl_29379 : CNF.NClause := [(52,false),(67,false),(21,false),(88,false),(79,false),(85,false),(73,true)]
theorem der_29379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29379 :=
  CNF.rup_sound cl_29379 [cl_6665,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6665 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29380 : CNF.NClause := [(52,false),(79,true),(21,false),(66,false),(67,false),(85,false),(88,false)]
theorem der_29380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29380 :=
  CNF.rup_sound cl_29380 [cl_6681,cl_29074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6681 v h) (hints_cons _ _ _ (der_29074 v h) (by intro d hd; cases hd)))
def cl_29381 : CNF.NClause := [(52,false),(67,false),(21,false),(66,false),(88,false),(79,false),(85,true)]
theorem der_29381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29381 :=
  CNF.rup_sound cl_29381 [cl_6697,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6697 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29382 : CNF.NClause := [(52,false),(79,true),(21,false),(73,true),(67,false),(85,true),(88,false)]
theorem der_29382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29382 :=
  CNF.rup_sound cl_29382 [cl_6713,cl_29195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6713 v h) (hints_cons _ _ _ (der_29195 v h) (by intro d hd; cases hd)))
def cl_29383 : CNF.NClause := [(52,false),(88,true),(21,false),(73,true),(67,false),(85,false),(79,false)]
theorem der_29383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29383 :=
  CNF.rup_sound cl_29383 [cl_6729,cl_29197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6729 v h) (hints_cons _ _ _ (der_29197 v h) (by intro d hd; cases hd)))
def cl_29384 : CNF.NClause := [(52,false),(79,true),(21,false),(73,true),(67,false),(85,false),(88,true)]
theorem der_29384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29384 :=
  CNF.rup_sound cl_29384 [cl_6745,cl_29199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6745 v h) (hints_cons _ _ _ (der_29199 v h) (by intro d hd; cases hd)))
def cl_29385 : CNF.NClause := [(52,false),(88,true),(21,false),(66,false),(67,false),(79,false),(85,true)]
theorem der_29385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29385 :=
  CNF.rup_sound cl_29385 [cl_6761,cl_29069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6761 v h) (hints_cons _ _ _ (der_29069 v h) (by intro d hd; cases hd)))
def cl_29386 : CNF.NClause := [(52,false),(79,true),(21,false),(66,false),(67,false),(85,true),(88,true)]
theorem der_29386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29386 :=
  CNF.rup_sound cl_29386 [cl_6777,cl_29069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6777 v h) (hints_cons _ _ _ (der_29069 v h) (by intro d hd; cases hd)))
def cl_29387 : CNF.NClause := [(52,false),(67,false),(88,false),(66,false),(79,false),(85,false),(73,true)]
theorem der_29387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29387 :=
  CNF.rup_sound cl_29387 [cl_6666,cl_29379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6666 v h) (hints_cons _ _ _ (der_29379 v h) (by intro d hd; cases hd)))
def cl_29388 : CNF.NClause := [(52,false),(79,true),(21,true),(67,false),(66,false),(85,false),(88,false)]
theorem der_29388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29388 :=
  CNF.rup_sound cl_29388 [cl_6682,cl_29074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6682 v h) (hints_cons _ _ _ (der_29074 v h) (by intro d hd; cases hd)))
def cl_29389 : CNF.NClause := [(52,false),(67,false),(21,true),(88,false),(66,false),(79,false),(85,true)]
theorem der_29389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29389 :=
  CNF.rup_sound cl_29389 [cl_6698,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6698 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29390 : CNF.NClause := [(52,false),(79,true),(21,true),(67,false),(73,true),(85,true),(88,false)]
theorem der_29390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29390 :=
  CNF.rup_sound cl_29390 [cl_6714,cl_29226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6714 v h) (hints_cons _ _ _ (der_29226 v h) (by intro d hd; cases hd)))
def cl_29391 : CNF.NClause := [(52,false),(88,true),(21,true),(67,false),(73,true),(85,false),(79,false)]
theorem der_29391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29391 :=
  CNF.rup_sound cl_29391 [cl_6730,cl_29230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6730 v h) (hints_cons _ _ _ (der_29230 v h) (by intro d hd; cases hd)))
def cl_29392 : CNF.NClause := [(52,false),(79,true),(21,true),(67,false),(73,true),(85,false),(88,true)]
theorem der_29392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29392 :=
  CNF.rup_sound cl_29392 [cl_6746,cl_29234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6746 v h) (hints_cons _ _ _ (der_29234 v h) (by intro d hd; cases hd)))
def cl_29393 : CNF.NClause := [(52,false),(88,true),(21,true),(67,false),(66,false),(73,true),(79,false)]
theorem der_29393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29393 :=
  CNF.rup_sound cl_29393 [cl_6762,cl_29391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6762 v h) (hints_cons _ _ _ (der_29391 v h) (by intro d hd; cases hd)))
def cl_29394 : CNF.NClause := [(52,false),(79,true),(21,true),(67,false),(66,false),(85,true),(88,true)]
theorem der_29394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29394 :=
  CNF.rup_sound cl_29394 [cl_6778,cl_29077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6778 v h) (hints_cons _ _ _ (der_29077 v h) (by intro d hd; cases hd)))
def cl_29395 : CNF.NClause := [(49,false),(69,false),(18,true),(77,false),(86,false),(91,false),(65,false)]
theorem der_29395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29395 :=
  CNF.rup_sound cl_29395 [cl_6282,cl_26727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6282 v h) (hints_cons _ _ _ (der_26727 v h) (by intro d hd; cases hd)))
def cl_29396 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,true),(86,false),(91,false)]
theorem der_29396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29396 :=
  CNF.rup_sound cl_29396 [cl_6298,cl_29345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6298 v h) (hints_cons _ _ _ (der_29345 v h) (by intro d hd; cases hd)))
def cl_29397 : CNF.NClause := [(49,false),(18,true),(69,false),(65,false),(86,true),(77,false),(91,false)]
theorem der_29397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29397 :=
  CNF.rup_sound cl_29397 [cl_6314,cl_29053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6314 v h) (hints_cons _ _ _ (der_29053 v h) (by intro d hd; cases hd)))
def cl_29398 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(65,false),(86,true),(91,false)]
theorem der_29398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29398 :=
  CNF.rup_sound cl_29398 [cl_6330,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6330 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_29399 : CNF.NClause := [(49,false),(18,true),(86,false),(65,false),(69,false),(91,true),(77,false)]
theorem der_29399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29399 :=
  CNF.rup_sound cl_29399 [cl_6346,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6346 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29400 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(65,false),(86,false),(91,true)]
theorem der_29400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29400 :=
  CNF.rup_sound cl_29400 [cl_6362,cl_26729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6362 v h) (hints_cons _ _ _ (der_26729 v h) (by intro d hd; cases hd)))
def cl_29401 : CNF.NClause := [(49,false),(73,true),(18,true),(69,false),(86,true),(77,false),(91,true)]
theorem der_29401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29401 :=
  CNF.rup_sound cl_29401 [cl_6378,cl_29365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6378 v h) (hints_cons _ _ _ (der_29365 v h) (by intro d hd; cases hd)))
def cl_29402 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(65,false),(86,true),(91,true)]
theorem der_29402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29402 :=
  CNF.rup_sound cl_29402 [cl_6394,cl_29050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6394 v h) (hints_cons _ _ _ (der_29050 v h) (by intro d hd; cases hd)))
def cl_29403 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(89,true),(79,false)]
theorem der_29403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29403 :=
  CNF.rup_sound cl_29403 [cl_5825,cl_29045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5825 v h) (hints_cons _ _ _ (der_29045 v h) (by intro d hd; cases hd)))
def cl_29404 : CNF.NClause := [(47,false),(16,false),(66,false),(89,true),(84,false),(75,false),(77,false)]
theorem der_29404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29404 :=
  CNF.rup_sound cl_29404 [cl_6081,cl_29134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6081 v h) (hints_cons _ _ _ (der_29134 v h) (by intro d hd; cases hd)))
def cl_29405 : CNF.NClause := [(47,false),(68,false),(77,false),(89,true),(84,false),(75,false),(66,false)]
theorem der_29405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29405 :=
  CNF.rup_sound cl_29405 [cl_6082,cl_29404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6082 v h) (hints_cons _ _ _ (der_29404 v h) (by intro d hd; cases hd)))
def cl_29406 : CNF.NClause := [(47,false),(77,true),(16,false),(66,false),(68,false),(89,true),(75,false)]
theorem der_29406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29406 :=
  CNF.rup_sound cl_29406 [cl_6097,cl_29066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6097 v h) (hints_cons _ _ _ (der_29066 v h) (by intro d hd; cases hd)))
def cl_29407 : CNF.NClause := [(47,false),(77,true),(66,false),(16,true),(89,true),(75,false),(68,false)]
theorem der_29407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29407 :=
  CNF.rup_sound cl_29407 [cl_6098,cl_29066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6098 v h) (hints_cons _ _ _ (der_29066 v h) (by intro d hd; cases hd)))
def cl_29408 : CNF.NClause := [(45,false),(70,false),(14,true),(86,false),(63,false),(72,false),(79,false)]
theorem der_29408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29408 :=
  CNF.rup_sound cl_29408 [cl_5826,cl_5762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5826 v h) (hints_cons _ _ _ (inp_5762 v h) (by intro d hd; cases hd)))
def cl_29409 : CNF.NClause := [(44,false),(71,true),(13,true),(88,false),(84,false),(78,false),(72,false)]
theorem der_29409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29409 :=
  CNF.rup_sound cl_29409 [cl_5638,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5638 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29410 : CNF.NClause := [(44,false),(71,true),(78,false),(72,false),(88,false),(65,false),(84,false)]
theorem der_29410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29410 :=
  CNF.rup_sound cl_29410 [cl_5637,cl_29409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5637 v h) (hints_cons _ _ _ (der_29409 v h) (by intro d hd; cases hd)))
def cl_29411 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(84,false),(78,false),(88,false)]
theorem der_29411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29411 :=
  CNF.rup_sound cl_29411 [cl_5645,cl_29410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5645 v h) (hints_cons _ _ _ (der_29410 v h) (by intro d hd; cases hd)))
def cl_29412 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(72,false),(84,false),(88,false)]
theorem der_29412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29412 :=
  CNF.rup_sound cl_29412 [cl_5653,cl_29086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5653 v h) (hints_cons _ _ _ (der_29086 v h) (by intro d hd; cases hd)))
def cl_29413 : CNF.NClause := [(44,false),(78,true),(13,false),(72,true),(71,true),(84,false),(88,false)]
theorem der_29413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29413 :=
  CNF.rup_sound cl_29413 [cl_5661,cl_29314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5661 v h) (hints_cons _ _ _ (der_29314 v h) (by intro d hd; cases hd)))
def cl_29414 : CNF.NClause := [(44,false),(84,true),(13,false),(65,false),(72,false),(78,false),(88,false)]
theorem der_29414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29414 :=
  CNF.rup_sound cl_29414 [cl_5669,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5669 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29415 : CNF.NClause := [(44,false),(84,true),(13,false),(72,true),(71,true),(78,false),(88,false)]
theorem der_29415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29415 :=
  CNF.rup_sound cl_29415 [cl_5677,cl_29318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5677 v h) (hints_cons _ _ _ (der_29318 v h) (by intro d hd; cases hd)))
def cl_29416 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(72,false),(84,true),(88,false)]
theorem der_29416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29416 :=
  CNF.rup_sound cl_29416 [cl_5685,cl_29087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5685 v h) (hints_cons _ _ _ (der_29087 v h) (by intro d hd; cases hd)))
def cl_29417 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(72,true),(71,true),(88,false)]
theorem der_29417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29417 :=
  CNF.rup_sound cl_29417 [cl_5693,cl_29413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5693 v h) (hints_cons _ _ _ (der_29413 v h) (by intro d hd; cases hd)))
def cl_29418 : CNF.NClause := [(44,false),(88,true),(13,false),(84,false),(78,false),(72,false),(71,true)]
theorem der_29418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29418 :=
  CNF.rup_sound cl_29418 [cl_5701,cl_29324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5701 v h) (hints_cons _ _ _ (der_29324 v h) (by intro d hd; cases hd)))
def cl_29419 : CNF.NClause := [(44,false),(88,true),(13,false),(72,true),(71,true),(78,false),(84,false)]
theorem der_29419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29419 :=
  CNF.rup_sound cl_29419 [cl_5709,cl_29326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5709 v h) (hints_cons _ _ _ (der_29326 v h) (by intro d hd; cases hd)))
def cl_29420 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(72,false),(84,false),(88,true)]
theorem der_29420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29420 :=
  CNF.rup_sound cl_29420 [cl_5717,cl_29088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5717 v h) (hints_cons _ _ _ (der_29088 v h) (by intro d hd; cases hd)))
def cl_29421 : CNF.NClause := [(44,false),(78,true),(13,false),(72,true),(71,true),(84,false),(88,true)]
theorem der_29421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29421 :=
  CNF.rup_sound cl_29421 [cl_5725,cl_29330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5725 v h) (hints_cons _ _ _ (der_29330 v h) (by intro d hd; cases hd)))
def cl_29422 : CNF.NClause := [(44,false),(88,true),(13,false),(65,false),(72,false),(78,false),(84,true)]
theorem der_29422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29422 :=
  CNF.rup_sound cl_29422 [cl_5733,cl_29059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5733 v h) (hints_cons _ _ _ (der_29059 v h) (by intro d hd; cases hd)))
def cl_29423 : CNF.NClause := [(44,false),(88,true),(13,false),(72,true),(71,true),(78,false),(84,true)]
theorem der_29423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29423 :=
  CNF.rup_sound cl_29423 [cl_5741,cl_29334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5741 v h) (hints_cons _ _ _ (der_29334 v h) (by intro d hd; cases hd)))
def cl_29424 : CNF.NClause := [(44,false),(78,true),(13,false),(72,false),(71,true),(84,true),(88,true)]
theorem der_29424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29424 :=
  CNF.rup_sound cl_29424 [cl_5749,cl_29336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5749 v h) (hints_cons _ _ _ (der_29336 v h) (by intro d hd; cases hd)))
def cl_29425 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(72,true),(71,true),(84,true)]
theorem der_29425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29425 :=
  CNF.rup_sound cl_29425 [cl_5757,cl_29417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5757 v h) (hints_cons _ _ _ (der_29417 v h) (by intro d hd; cases hd)))
def cl_29426 : CNF.NClause := [(44,false),(88,false),(72,true),(13,true),(78,false),(84,false),(71,true)]
theorem der_29426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29426 :=
  CNF.rup_sound cl_29426 [cl_5646,cl_29310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5646 v h) (hints_cons _ _ _ (der_29310 v h) (by intro d hd; cases hd)))
def cl_29427 : CNF.NClause := [(44,false),(78,true),(65,false),(13,true),(72,false),(84,false),(88,false)]
theorem der_29427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29427 :=
  CNF.rup_sound cl_29427 [cl_5654,cl_29086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5654 v h) (hints_cons _ _ _ (der_29086 v h) (by intro d hd; cases hd)))
def cl_29428 : CNF.NClause := [(44,false),(78,true),(13,true),(72,true),(71,true),(84,false),(88,false)]
theorem der_29428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29428 :=
  CNF.rup_sound cl_29428 [cl_5662,cl_29251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5662 v h) (hints_cons _ _ _ (der_29251 v h) (by intro d hd; cases hd)))
def cl_29429 : CNF.NClause := [(44,false),(84,true),(65,false),(13,true),(72,false),(78,false),(88,false)]
theorem der_29429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29429 :=
  CNF.rup_sound cl_29429 [cl_5670,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5670 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29430 : CNF.NClause := [(44,false),(84,true),(13,true),(72,true),(71,true),(78,false),(88,false)]
theorem der_29430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29430 :=
  CNF.rup_sound cl_29430 [cl_5678,cl_29255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5678 v h) (hints_cons _ _ _ (der_29255 v h) (by intro d hd; cases hd)))
def cl_29431 : CNF.NClause := [(44,false),(78,true),(13,true),(72,false),(71,true),(84,true),(88,false)]
theorem der_29431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29431 :=
  CNF.rup_sound cl_29431 [cl_5686,cl_29257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5686 v h) (hints_cons _ _ _ (der_29257 v h) (by intro d hd; cases hd)))
def cl_29432 : CNF.NClause := [(44,false),(78,true),(13,true),(72,true),(71,true),(84,true),(88,false)]
theorem der_29432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29432 :=
  CNF.rup_sound cl_29432 [cl_5694,cl_29259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5694 v h) (hints_cons _ _ _ (der_29259 v h) (by intro d hd; cases hd)))
def cl_29433 : CNF.NClause := [(44,false),(88,true),(13,true),(72,false),(78,false),(71,true),(84,false)]
theorem der_29433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29433 :=
  CNF.rup_sound cl_29433 [cl_5702,cl_29261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5702 v h) (hints_cons _ _ _ (der_29261 v h) (by intro d hd; cases hd)))
def cl_29434 : CNF.NClause := [(44,false),(88,true),(13,true),(72,true),(71,true),(78,false),(84,false)]
theorem der_29434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29434 :=
  CNF.rup_sound cl_29434 [cl_5710,cl_29263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5710 v h) (hints_cons _ _ _ (der_29263 v h) (by intro d hd; cases hd)))
def cl_29435 : CNF.NClause := [(44,false),(78,true),(13,true),(72,false),(71,true),(84,false),(88,true)]
theorem der_29435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29435 :=
  CNF.rup_sound cl_29435 [cl_5718,cl_29265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5718 v h) (hints_cons _ _ _ (der_29265 v h) (by intro d hd; cases hd)))
def cl_29436 : CNF.NClause := [(44,false),(78,true),(13,true),(72,true),(71,true),(84,false),(88,true)]
theorem der_29436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29436 :=
  CNF.rup_sound cl_29436 [cl_5726,cl_29267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5726 v h) (hints_cons _ _ _ (der_29267 v h) (by intro d hd; cases hd)))
def cl_29437 : CNF.NClause := [(44,false),(84,true),(13,true),(72,false),(78,false),(71,true),(88,true)]
theorem der_29437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29437 :=
  CNF.rup_sound cl_29437 [cl_5734,cl_29269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5734 v h) (hints_cons _ _ _ (der_29269 v h) (by intro d hd; cases hd)))
def cl_29438 : CNF.NClause := [(44,false),(65,false),(13,true),(72,true),(71,true),(78,false),(84,true)]
theorem der_29438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29438 :=
  CNF.rup_sound cl_29438 [cl_5742,cl_29430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5742 v h) (hints_cons _ _ _ (der_29430 v h) (by intro d hd; cases hd)))
def cl_29439 : CNF.NClause := [(44,false),(78,true),(13,true),(72,false),(71,true),(84,true),(88,true)]
theorem der_29439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29439 :=
  CNF.rup_sound cl_29439 [cl_5750,cl_29336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5750 v h) (hints_cons _ _ _ (der_29336 v h) (by intro d hd; cases hd)))
def cl_29440 : CNF.NClause := [(44,false),(78,true),(13,true),(72,true),(71,true),(84,true),(88,true)]
theorem der_29440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29440 :=
  CNF.rup_sound cl_29440 [cl_5758,cl_29275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5758 v h) (hints_cons _ _ _ (der_29275 v h) (by intro d hd; cases hd)))
def cl_29441 : CNF.NClause := [(44,false),(88,true),(13,false),(71,false),(78,false),(65,false),(72,false)]
theorem der_29441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29441 :=
  CNF.rup_sound cl_29441 [cl_5697,cl_29059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5697 v h) (hints_cons _ _ _ (der_29059 v h) (by intro d hd; cases hd)))
def cl_29442 : CNF.NClause := [(44,false),(65,false),(13,true),(72,false),(78,false),(84,false),(71,false)]
theorem der_29442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29442 :=
  CNF.rup_sound cl_29442 [cl_5698,cl_26761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5698 v h) (hints_cons _ _ _ (der_26761 v h) (by intro d hd; cases hd)))
def cl_29443 : CNF.NClause := [(52,false),(88,true),(21,true),(79,false),(73,false),(67,false),(85,false)]
theorem der_29443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29443 :=
  CNF.rup_sound cl_29443 [cl_6722,cl_29228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6722 v h) (hints_cons _ _ _ (der_29228 v h) (by intro d hd; cases hd)))
def cl_29444 : CNF.NClause := [(47,false),(66,true),(16,true),(75,true),(77,false),(84,false),(89,false)]
theorem der_29444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29444 :=
  CNF.rup_sound cl_29444 [cl_6028,cl_29143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6028 v h) (hints_cons _ _ _ (der_29143 v h) (by intro d hd; cases hd)))
def cl_29445 : CNF.NClause := [(47,false),(66,true),(16,true),(75,true),(77,true),(84,false),(89,false)]
theorem der_29445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29445 :=
  CNF.rup_sound cl_29445 [cl_6044,cl_29164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6044 v h) (hints_cons _ _ _ (der_29164 v h) (by intro d hd; cases hd)))
def cl_29446 : CNF.NClause := [(47,false),(66,true),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem der_29446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29446 :=
  CNF.rup_sound cl_29446 [cl_6060,cl_29167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6060 v h) (hints_cons _ _ _ (der_29167 v h) (by intro d hd; cases hd)))
def cl_29447 : CNF.NClause := [(47,false),(66,true),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem der_29447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29447 :=
  CNF.rup_sound cl_29447 [cl_6076,cl_29171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6076 v h) (hints_cons _ _ _ (der_29171 v h) (by intro d hd; cases hd)))
def cl_29448 : CNF.NClause := [(47,false),(66,true),(16,true),(75,true),(77,false),(84,false),(89,true)]
theorem der_29448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29448 :=
  CNF.rup_sound cl_29448 [cl_6092,cl_29151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6092 v h) (hints_cons _ _ _ (der_29151 v h) (by intro d hd; cases hd)))
def cl_29449 : CNF.NClause := [(47,false),(66,true),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem der_29449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29449 :=
  CNF.rup_sound cl_29449 [cl_6108,cl_29179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6108 v h) (hints_cons _ _ _ (der_29179 v h) (by intro d hd; cases hd)))
def cl_29450 : CNF.NClause := [(47,false),(66,true),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem der_29450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29450 :=
  CNF.rup_sound cl_29450 [cl_6124,cl_29183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6124 v h) (hints_cons _ _ _ (der_29183 v h) (by intro d hd; cases hd)))
def cl_29451 : CNF.NClause := [(47,false),(66,true),(16,true),(68,false),(75,true),(77,true),(89,true)]
theorem der_29451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29451 :=
  CNF.rup_sound cl_29451 [cl_6140,cl_29449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6140 v h) (hints_cons _ _ _ (der_29449 v h) (by intro d hd; cases hd)))
def cl_29452 : CNF.NClause := [(53,false),(75,true),(86,false),(64,false),(67,false),(78,false),(90,false)]
theorem der_29452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29452 :=
  CNF.rup_sound cl_29452 [cl_6793,cl_26774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6793 v h) (hints_cons _ _ _ (der_26774 v h) (by intro d hd; cases hd)))
def cl_29453 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(67,false),(86,false),(90,false)]
theorem der_29453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29453 :=
  CNF.rup_sound cl_29453 [cl_6809,cl_29082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6809 v h) (hints_cons _ _ _ (der_29082 v h) (by intro d hd; cases hd)))
def cl_29454 : CNF.NClause := [(53,false),(64,false),(22,false),(67,false),(78,false),(86,true),(90,false)]
theorem der_29454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29454 :=
  CNF.rup_sound cl_29454 [cl_6825,cl_29042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6825 v h) (hints_cons _ _ _ (der_29042 v h) (by intro d hd; cases hd)))
def cl_29455 : CNF.NClause := [(53,false),(78,true),(64,false),(67,false),(75,true),(86,true),(90,false)]
theorem der_29455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29455 :=
  CNF.rup_sound cl_29455 [cl_6841,cl_26772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6841 v h) (hints_cons _ _ _ (der_26772 v h) (by intro d hd; cases hd)))
def cl_29456 : CNF.NClause := [(53,false),(64,false),(22,false),(67,false),(78,false),(86,false),(90,true)]
theorem der_29456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29456 :=
  CNF.rup_sound cl_29456 [cl_6857,cl_29039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6857 v h) (hints_cons _ _ _ (der_29039 v h) (by intro d hd; cases hd)))
def cl_29457 : CNF.NClause := [(53,false),(78,true),(64,false),(67,false),(75,true),(86,false),(90,true)]
theorem der_29457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29457 :=
  CNF.rup_sound cl_29457 [cl_6873,cl_26776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6873 v h) (hints_cons _ _ _ (der_26776 v h) (by intro d hd; cases hd)))
def cl_29458 : CNF.NClause := [(53,false),(90,true),(64,false),(22,false),(67,false),(86,true),(78,false)]
theorem der_29458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29458 :=
  CNF.rup_sound cl_29458 [cl_6889,cl_29043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6889 v h) (hints_cons _ _ _ (der_29043 v h) (by intro d hd; cases hd)))
def cl_29459 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(67,false),(86,true),(90,true)]
theorem der_29459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29459 :=
  CNF.rup_sound cl_29459 [cl_6905,cl_29085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6905 v h) (hints_cons _ _ _ (der_29085 v h) (by intro d hd; cases hd)))
def cl_29460 : CNF.NClause := [(47,false),(75,true),(16,false),(66,false),(77,false),(84,false),(89,false)]
theorem der_29460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29460 :=
  CNF.rup_sound cl_29460 [cl_6025,cl_29127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6025 v h) (hints_cons _ _ _ (der_29127 v h) (by intro d hd; cases hd)))
def cl_29461 : CNF.NClause := [(47,false),(75,true),(16,false),(68,false),(77,true),(84,false),(89,false)]
theorem der_29461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29461 :=
  CNF.rup_sound cl_29461 [cl_6041,cl_29179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6041 v h) (hints_cons _ _ _ (der_29179 v h) (by intro d hd; cases hd)))
def cl_29462 : CNF.NClause := [(47,false),(84,true),(16,false),(66,false),(68,false),(77,false),(89,false)]
theorem der_29462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29462 :=
  CNF.rup_sound cl_29462 [cl_6057,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6057 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29463 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(77,true),(75,true),(89,false)]
theorem der_29463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29463 :=
  CNF.rup_sound cl_29463 [cl_6073,cl_29461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6073 v h) (hints_cons _ _ _ (der_29461 v h) (by intro d hd; cases hd)))
def cl_29464 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(77,false),(84,false),(89,true)]
theorem der_29464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29464 :=
  CNF.rup_sound cl_29464 [cl_6089,cl_29404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6089 v h) (hints_cons _ _ _ (der_29404 v h) (by intro d hd; cases hd)))
def cl_29465 : CNF.NClause := [(47,false),(75,true),(16,false),(68,false),(77,true),(84,false),(89,true)]
theorem der_29465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29465 :=
  CNF.rup_sound cl_29465 [cl_6105,cl_29179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6105 v h) (hints_cons _ _ _ (der_29179 v h) (by intro d hd; cases hd)))
def cl_29466 : CNF.NClause := [(47,false),(84,true),(16,false),(66,false),(68,false),(77,false),(89,true)]
theorem der_29466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29466 :=
  CNF.rup_sound cl_29466 [cl_6121,cl_29060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6121 v h) (hints_cons _ _ _ (der_29060 v h) (by intro d hd; cases hd)))
def cl_29467 : CNF.NClause := [(47,false),(84,true),(16,false),(66,false),(68,false),(77,true),(89,true)]
theorem der_29467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29467 :=
  CNF.rup_sound cl_29467 [cl_6137,cl_29066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6137 v h) (hints_cons _ _ _ (der_29066 v h) (by intro d hd; cases hd)))
def cl_29468 : CNF.NClause := [(53,false),(75,true),(22,true),(78,false),(67,false),(86,false),(90,false)]
theorem der_29468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29468 :=
  CNF.rup_sound cl_29468 [cl_6796,cl_29452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6796 v h) (hints_cons _ _ _ (der_29452 v h) (by intro d hd; cases hd)))
def cl_29469 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(67,false),(86,false),(90,false)]
theorem der_29469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29469 :=
  CNF.rup_sound cl_29469 [cl_6812,cl_29090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6812 v h) (hints_cons _ _ _ (der_29090 v h) (by intro d hd; cases hd)))
def cl_29470 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(78,false),(86,true),(90,false)]
theorem der_29470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29470 :=
  CNF.rup_sound cl_29470 [cl_6828,cl_29047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6828 v h) (hints_cons _ _ _ (der_29047 v h) (by intro d hd; cases hd)))
def cl_29471 : CNF.NClause := [(53,false),(78,true),(22,true),(67,false),(75,true),(86,true),(90,false)]
theorem der_29471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29471 :=
  CNF.rup_sound cl_29471 [cl_6844,cl_29455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6844 v h) (hints_cons _ _ _ (der_29455 v h) (by intro d hd; cases hd)))
def cl_29472 : CNF.NClause := [(53,false),(75,true),(22,true),(67,false),(78,false),(86,false),(90,true)]
theorem der_29472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29472 :=
  CNF.rup_sound cl_29472 [cl_6860,cl_26774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6860 v h) (hints_cons _ _ _ (der_26774 v h) (by intro d hd; cases hd)))
def cl_29473 : CNF.NClause := [(53,false),(78,true),(22,true),(67,false),(75,true),(86,false),(90,true)]
theorem der_29473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29473 :=
  CNF.rup_sound cl_29473 [cl_6876,cl_29457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6876 v h) (hints_cons _ _ _ (der_29457 v h) (by intro d hd; cases hd)))
def cl_29474 : CNF.NClause := [(53,false),(90,true),(22,true),(64,true),(67,false),(86,true),(78,false)]
theorem der_29474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29474 :=
  CNF.rup_sound cl_29474 [cl_6892,cl_29048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6892 v h) (hints_cons _ _ _ (der_29048 v h) (by intro d hd; cases hd)))
def cl_29475 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(67,false),(75,true),(86,true)]
theorem der_29475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29475 :=
  CNF.rup_sound cl_29475 [cl_6908,cl_29471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6908 v h) (hints_cons _ _ _ (der_29471 v h) (by intro d hd; cases hd)))
def cl_29476 : CNF.NClause := [(47,false),(75,true),(77,false),(89,false),(16,true),(84,false),(66,false)]
theorem der_29476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29476 :=
  CNF.rup_sound cl_29476 [cl_6026,cl_26307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6026 v h) (hints_cons _ _ _ (der_26307 v h) (by intro d hd; cases hd)))
def cl_29477 : CNF.NClause := [(47,false),(75,true),(66,false),(68,false),(77,true),(84,false),(89,false)]
theorem der_29477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29477 :=
  CNF.rup_sound cl_29477 [cl_6042,cl_29463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6042 v h) (hints_cons _ _ _ (der_29463 v h) (by intro d hd; cases hd)))
def cl_29478 : CNF.NClause := [(47,false),(84,true),(66,false),(16,true),(77,false),(68,false),(89,false)]
theorem der_29478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29478 :=
  CNF.rup_sound cl_29478 [cl_6058,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6058 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29479 : CNF.NClause := [(47,false),(75,true),(66,false),(68,false),(77,true),(84,true),(89,false)]
theorem der_29479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29479 :=
  CNF.rup_sound cl_29479 [cl_6074,cl_29463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6074 v h) (hints_cons _ _ _ (der_29463 v h) (by intro d hd; cases hd)))
def cl_29480 : CNF.NClause := [(47,false),(75,true),(66,false),(68,false),(77,false),(84,false),(89,true)]
theorem der_29480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29480 :=
  CNF.rup_sound cl_29480 [cl_6090,cl_29464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6090 v h) (hints_cons _ _ _ (der_29464 v h) (by intro d hd; cases hd)))
def cl_29481 : CNF.NClause := [(47,false),(75,true),(68,false),(16,true),(77,true),(84,false),(89,true)]
theorem der_29481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29481 :=
  CNF.rup_sound cl_29481 [cl_6106,cl_29449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6106 v h) (hints_cons _ _ _ (der_29449 v h) (by intro d hd; cases hd)))
def cl_29482 : CNF.NClause := [(47,false),(84,true),(66,false),(68,false),(77,false),(75,true),(89,true)]
theorem der_29482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29482 :=
  CNF.rup_sound cl_29482 [cl_6122,cl_29466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6122 v h) (hints_cons _ _ _ (der_29466 v h) (by intro d hd; cases hd)))
def cl_29483 : CNF.NClause := [(47,false),(66,false),(68,false),(16,true),(77,true),(84,true),(89,true)]
theorem der_29483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29483 :=
  CNF.rup_sound cl_29483 [cl_6138,cl_29066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6138 v h) (hints_cons _ _ _ (der_29066 v h) (by intro d hd; cases hd)))
def cl_29484 : CNF.NClause := [(45,false),(72,true),(14,false),(86,false),(63,false),(79,false),(89,false)]
theorem der_29484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29484 :=
  CNF.rup_sound cl_29484 [cl_5769,cl_29103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5769 v h) (hints_cons _ _ _ (der_29103 v h) (by intro d hd; cases hd)))
def cl_29485 : CNF.NClause := [(45,false),(79,true),(14,false),(63,false),(70,false),(86,false),(89,false)]
theorem der_29485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29485 :=
  CNF.rup_sound cl_29485 [cl_5785,cl_29078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5785 v h) (hints_cons _ _ _ (der_29078 v h) (by intro d hd; cases hd)))
def cl_29486 : CNF.NClause := [(45,false),(89,false),(14,false),(63,false),(79,false),(70,false),(86,true)]
theorem der_29486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29486 :=
  CNF.rup_sound cl_29486 [cl_5801,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5801 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29487 : CNF.NClause := [(45,false),(89,false),(14,false),(63,false),(79,true),(70,false),(86,true)]
theorem der_29487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29487 :=
  CNF.rup_sound cl_29487 [cl_5817,cl_29070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5817 v h) (hints_cons _ _ _ (der_29070 v h) (by intro d hd; cases hd)))
def cl_29488 : CNF.NClause := [(45,false),(89,true),(14,false),(63,false),(79,false),(86,false),(72,true)]
theorem der_29488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29488 :=
  CNF.rup_sound cl_29488 [cl_5833,cl_29103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5833 v h) (hints_cons _ _ _ (der_29103 v h) (by intro d hd; cases hd)))
def cl_29489 : CNF.NClause := [(45,false),(79,true),(14,false),(63,false),(72,true),(86,false),(89,true)]
theorem der_29489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29489 :=
  CNF.rup_sound cl_29489 [cl_5849,cl_29105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5849 v h) (hints_cons _ _ _ (der_29105 v h) (by intro d hd; cases hd)))
def cl_29490 : CNF.NClause := [(45,false),(14,false),(63,false),(72,true),(79,false),(70,false),(89,true)]
theorem der_29490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29490 :=
  CNF.rup_sound cl_29490 [cl_5865,cl_29488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5865 v h) (hints_cons _ _ _ (der_29488 v h) (by intro d hd; cases hd)))
def cl_29491 : CNF.NClause := [(45,false),(86,true),(14,false),(63,false),(79,true),(70,false),(89,true)]
theorem der_29491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29491 :=
  CNF.rup_sound cl_29491 [cl_5881,cl_29081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5881 v h) (hints_cons _ _ _ (der_29081 v h) (by intro d hd; cases hd)))
def cl_29492 : CNF.NClause := [(45,false),(63,true),(14,true),(72,true),(79,false),(86,false),(89,false)]
theorem der_29492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29492 :=
  CNF.rup_sound cl_29492 [cl_5772,cl_29111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5772 v h) (hints_cons _ _ _ (der_29111 v h) (by intro d hd; cases hd)))
def cl_29493 : CNF.NClause := [(45,false),(79,true),(14,true),(70,false),(63,true),(86,false),(89,false)]
theorem der_29493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29493 :=
  CNF.rup_sound cl_29493 [cl_5788,cl_5780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5788 v h) (hints_cons _ _ _ (inp_5780 v h) (by intro d hd; cases hd)))
def cl_29494 : CNF.NClause := [(45,false),(89,false),(14,true),(63,true),(72,true),(79,false),(86,true)]
theorem der_29494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29494 :=
  CNF.rup_sound cl_29494 [cl_5804,cl_29115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5804 v h) (hints_cons _ _ _ (der_29115 v h) (by intro d hd; cases hd)))
def cl_29495 : CNF.NClause := [(45,false),(89,false),(14,true),(63,true),(72,true),(79,true),(86,true)]
theorem der_29495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29495 :=
  CNF.rup_sound cl_29495 [cl_5820,cl_29117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5820 v h) (hints_cons _ _ _ (der_29117 v h) (by intro d hd; cases hd)))
def cl_29496 : CNF.NClause := [(44,false),(72,true),(13,false),(88,false),(78,false),(71,false),(84,false)]
theorem der_29496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29496 :=
  CNF.rup_sound cl_29496 [cl_5641,cl_29325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5641 v h) (hints_cons _ _ _ (der_29325 v h) (by intro d hd; cases hd)))
def cl_29497 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(71,false),(84,false),(88,false)]
theorem der_29497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29497 :=
  CNF.rup_sound cl_29497 [cl_5657,cl_29086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5657 v h) (hints_cons _ _ _ (der_29086 v h) (by intro d hd; cases hd)))
def cl_29498 : CNF.NClause := [(44,false),(84,true),(13,false),(65,false),(78,false),(71,false),(88,false)]
theorem der_29498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29498 :=
  CNF.rup_sound cl_29498 [cl_5673,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5673 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29499 : CNF.NClause := [(44,false),(78,true),(13,false),(72,true),(71,false),(84,true),(88,false)]
theorem der_29499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29499 :=
  CNF.rup_sound cl_29499 [cl_5689,cl_29321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5689 v h) (hints_cons _ _ _ (der_29321 v h) (by intro d hd; cases hd)))
def cl_29500 : CNF.NClause := [(44,false),(88,true),(13,false),(72,true),(78,false),(84,false),(71,false)]
theorem der_29500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29500 :=
  CNF.rup_sound cl_29500 [cl_5705,cl_29325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5705 v h) (hints_cons _ _ _ (der_29325 v h) (by intro d hd; cases hd)))
def cl_29501 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(71,false),(84,false),(88,true)]
theorem der_29501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29501 :=
  CNF.rup_sound cl_29501 [cl_5721,cl_29088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5721 v h) (hints_cons _ _ _ (der_29088 v h) (by intro d hd; cases hd)))
def cl_29502 : CNF.NClause := [(44,false),(88,true),(13,false),(65,false),(72,true),(78,false),(71,false)]
theorem der_29502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29502 :=
  CNF.rup_sound cl_29502 [cl_5737,cl_29500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5737 v h) (hints_cons _ _ _ (der_29500 v h) (by intro d hd; cases hd)))
def cl_29503 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(72,true),(71,false),(84,true)]
theorem der_29503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29503 :=
  CNF.rup_sound cl_29503 [cl_5753,cl_29499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5753 v h) (hints_cons _ _ _ (der_29499 v h) (by intro d hd; cases hd)))
def cl_29504 : CNF.NClause := [(45,false),(86,false),(14,true),(89,false),(63,false),(79,false),(70,false)]
theorem der_29504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29504 :=
  CNF.rup_sound cl_29504 [cl_5770,cl_29408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5770 v h) (hints_cons _ _ _ (der_29408 v h) (by intro d hd; cases hd)))
def cl_29505 : CNF.NClause := [(45,false),(79,true),(14,true),(89,false),(86,false),(63,false),(70,false)]
theorem der_29505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29505 :=
  CNF.rup_sound cl_29505 [cl_5786,cl_29078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5786 v h) (hints_cons _ _ _ (der_29078 v h) (by intro d hd; cases hd)))
def cl_29506 : CNF.NClause := [(45,false),(86,true),(14,true),(70,false),(79,false),(63,false),(89,false)]
theorem der_29506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29506 :=
  CNF.rup_sound cl_29506 [cl_5802,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5802 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29507 : CNF.NClause := [(45,false),(79,true),(14,true),(70,false),(72,true),(86,true),(89,false)]
theorem der_29507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29507 :=
  CNF.rup_sound cl_29507 [cl_5818,cl_29495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5818 v h) (hints_cons _ _ _ (der_29495 v h) (by intro d hd; cases hd)))
def cl_29508 : CNF.NClause := [(45,false),(86,false),(14,true),(89,true),(79,false),(70,false),(63,false)]
theorem der_29508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29508 :=
  CNF.rup_sound cl_29508 [cl_5834,cl_29408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5834 v h) (hints_cons _ _ _ (der_29408 v h) (by intro d hd; cases hd)))
def cl_29509 : CNF.NClause := [(45,false),(79,true),(14,true),(86,false),(70,false),(72,true),(63,false)]
theorem der_29509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29509 :=
  CNF.rup_sound cl_29509 [cl_5850,cl_29505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5850 v h) (hints_cons _ _ _ (der_29505 v h) (by intro d hd; cases hd)))
def cl_29510 : CNF.NClause := [(45,false),(70,false),(89,true),(72,true),(79,false),(63,false),(86,true)]
theorem der_29510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29510 :=
  CNF.rup_sound cl_29510 [cl_5866,cl_29490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5866 v h) (hints_cons _ _ _ (der_29490 v h) (by intro d hd; cases hd)))
def cl_29511 : CNF.NClause := [(45,false),(79,true),(14,true),(70,false),(63,false),(86,true),(89,true)]
theorem der_29511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29511 :=
  CNF.rup_sound cl_29511 [cl_5882,cl_29081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5882 v h) (hints_cons _ _ _ (der_29081 v h) (by intro d hd; cases hd)))
def cl_29512 : CNF.NClause := [(44,false),(88,false),(13,true),(84,false),(65,false),(71,false),(78,false)]
theorem der_29512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29512 :=
  CNF.rup_sound cl_29512 [cl_5642,cl_26761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5642 v h) (hints_cons _ _ _ (der_26761 v h) (by intro d hd; cases hd)))
def cl_29513 : CNF.NClause := [(44,false),(78,true),(65,false),(13,true),(71,false),(84,false),(88,false)]
theorem der_29513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29513 :=
  CNF.rup_sound cl_29513 [cl_5658,cl_29086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5658 v h) (hints_cons _ _ _ (der_29086 v h) (by intro d hd; cases hd)))
def cl_29514 : CNF.NClause := [(44,false),(84,true),(65,false),(13,true),(71,false),(78,false),(88,false)]
theorem der_29514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29514 :=
  CNF.rup_sound cl_29514 [cl_5674,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5674 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29515 : CNF.NClause := [(44,false),(78,true),(13,true),(72,true),(71,false),(84,true),(88,false)]
theorem der_29515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29515 :=
  CNF.rup_sound cl_29515 [cl_5690,cl_29321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5690 v h) (hints_cons _ _ _ (der_29321 v h) (by intro d hd; cases hd)))
def cl_29516 : CNF.NClause := [(44,false),(65,false),(13,true),(72,true),(71,false),(78,false),(84,false)]
theorem der_29516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29516 :=
  CNF.rup_sound cl_29516 [cl_5706,cl_29512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5706 v h) (hints_cons _ _ _ (der_29512 v h) (by intro d hd; cases hd)))
def cl_29517 : CNF.NClause := [(44,false),(65,false),(13,true),(72,true),(71,false),(84,false),(88,true)]
theorem der_29517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29517 :=
  CNF.rup_sound cl_29517 [cl_5722,cl_29516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5722 v h) (hints_cons _ _ _ (der_29516 v h) (by intro d hd; cases hd)))
def cl_29518 : CNF.NClause := [(44,false),(88,true),(65,false),(13,true),(72,true),(71,false),(78,false)]
theorem der_29518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29518 :=
  CNF.rup_sound cl_29518 [cl_5738,cl_29517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5738 v h) (hints_cons _ _ _ (der_29517 v h) (by intro d hd; cases hd)))
def cl_29519 : CNF.NClause := [(44,false),(78,true),(65,false),(13,true),(72,true),(71,false),(88,true)]
theorem der_29519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29519 :=
  CNF.rup_sound cl_29519 [cl_5754,cl_29517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5754 v h) (hints_cons _ _ _ (der_29517 v h) (by intro d hd; cases hd)))
def cl_29520 : CNF.NClause := [(49,false),(69,true),(18,false),(91,false),(77,false),(86,false),(73,false)]
theorem der_29520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29520 :=
  CNF.rup_sound cl_29520 [cl_6277,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6277 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29521 : CNF.NClause := [(49,false),(69,true),(18,false),(73,true),(77,false),(86,false),(91,false)]
theorem der_29521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29521 :=
  CNF.rup_sound cl_29521 [cl_6285,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6285 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29522 : CNF.NClause := [(49,false),(69,true),(18,false),(73,false),(77,true),(86,false),(91,false)]
theorem der_29522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29522 :=
  CNF.rup_sound cl_29522 [cl_6293,cl_29280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6293 v h) (hints_cons _ _ _ (der_29280 v h) (by intro d hd; cases hd)))
def cl_29523 : CNF.NClause := [(49,false),(69,true),(18,false),(73,true),(77,true),(86,false),(91,false)]
theorem der_29523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29523 :=
  CNF.rup_sound cl_29523 [cl_6301,cl_29282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6301 v h) (hints_cons _ _ _ (der_29282 v h) (by intro d hd; cases hd)))
def cl_29524 : CNF.NClause := [(49,false),(69,true),(18,false),(73,false),(77,false),(86,true),(91,false)]
theorem der_29524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29524 :=
  CNF.rup_sound cl_29524 [cl_6309,cl_29284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6309 v h) (hints_cons _ _ _ (der_29284 v h) (by intro d hd; cases hd)))
def cl_29525 : CNF.NClause := [(49,false),(69,true),(18,false),(73,true),(77,false),(86,true),(91,false)]
theorem der_29525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29525 :=
  CNF.rup_sound cl_29525 [cl_6317,cl_29286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6317 v h) (hints_cons _ _ _ (der_29286 v h) (by intro d hd; cases hd)))
def cl_29527 : CNF.NClause := [(49,false),(69,true),(18,false),(73,true),(77,true),(86,true),(91,false)]
theorem der_29527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29527 :=
  CNF.rup_sound cl_29527 [cl_6333,cl_29290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6333 v h) (hints_cons _ _ _ (der_29290 v h) (by intro d hd; cases hd)))
def cl_29528 : CNF.NClause := [(49,false),(18,false),(91,true),(65,false),(77,false),(86,false),(73,false)]
theorem der_29528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29528 :=
  CNF.rup_sound cl_29528 [cl_6341,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6341 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29530 : CNF.NClause := [(49,false),(69,true),(18,false),(73,false),(77,true),(86,false),(91,true)]
theorem der_29530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29530 :=
  CNF.rup_sound cl_29530 [cl_6357,cl_29296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6357 v h) (hints_cons _ _ _ (der_29296 v h) (by intro d hd; cases hd)))
def cl_29531 : CNF.NClause := [(49,false),(69,true),(18,false),(73,true),(77,true),(86,false),(91,true)]
theorem der_29531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29531 :=
  CNF.rup_sound cl_29531 [cl_6365,cl_29298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6365 v h) (hints_cons _ _ _ (der_29298 v h) (by intro d hd; cases hd)))
def cl_29532 : CNF.NClause := [(49,false),(69,true),(18,false),(73,false),(77,false),(86,true),(91,true)]
theorem der_29532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29532 :=
  CNF.rup_sound cl_29532 [cl_6373,cl_29300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6373 v h) (hints_cons _ _ _ (der_29300 v h) (by intro d hd; cases hd)))
def cl_29533 : CNF.NClause := [(49,false),(69,true),(18,false),(65,false),(73,true),(77,false),(86,true)]
theorem der_29533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29533 :=
  CNF.rup_sound cl_29533 [cl_6381,cl_29525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6381 v h) (hints_cons _ _ _ (der_29525 v h) (by intro d hd; cases hd)))
def cl_29534 : CNF.NClause := [(49,false),(18,false),(65,false),(73,false),(77,true),(86,true),(91,true)]
theorem der_29534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29534 :=
  CNF.rup_sound cl_29534 [cl_6389,cl_29303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6389 v h) (hints_cons _ _ _ (der_29303 v h) (by intro d hd; cases hd)))
def cl_29535 : CNF.NClause := [(49,false),(69,true),(18,false),(73,true),(77,true),(86,true),(91,true)]
theorem der_29535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29535 :=
  CNF.rup_sound cl_29535 [cl_6397,cl_29306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6397 v h) (hints_cons _ _ _ (der_29306 v h) (by intro d hd; cases hd)))
def cl_29536 : CNF.NClause := [(49,false),(18,true),(65,false),(73,false),(77,false),(86,false),(91,false)]
theorem der_29536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29536 :=
  CNF.rup_sound cl_29536 [cl_6278,cl_26727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6278 v h) (hints_cons _ _ _ (der_26727 v h) (by intro d hd; cases hd)))
def cl_29537 : CNF.NClause := [(49,false),(69,true),(18,true),(73,true),(77,false),(86,false),(91,false)]
theorem der_29537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29537 :=
  CNF.rup_sound cl_29537 [cl_6286,cl_29342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6286 v h) (hints_cons _ _ _ (der_29342 v h) (by intro d hd; cases hd)))
def cl_29538 : CNF.NClause := [(49,false),(18,true),(65,false),(73,false),(77,true),(86,false),(91,false)]
theorem der_29538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29538 :=
  CNF.rup_sound cl_29538 [cl_6294,cl_29049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6294 v h) (hints_cons _ _ _ (der_29049 v h) (by intro d hd; cases hd)))
def cl_29539 : CNF.NClause := [(49,false),(69,true),(65,false),(73,true),(77,true),(86,false),(91,false)]
theorem der_29539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29539 :=
  CNF.rup_sound cl_29539 [cl_6302,cl_29523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6302 v h) (hints_cons _ _ _ (der_29523 v h) (by intro d hd; cases hd)))
def cl_29540 : CNF.NClause := [(49,false),(69,true),(18,true),(73,false),(77,false),(86,true),(91,false)]
theorem der_29540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29540 :=
  CNF.rup_sound cl_29540 [cl_6310,cl_29348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6310 v h) (hints_cons _ _ _ (der_29348 v h) (by intro d hd; cases hd)))
def cl_29541 : CNF.NClause := [(49,false),(69,true),(18,true),(73,true),(77,false),(86,true),(91,false)]
theorem der_29541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29541 :=
  CNF.rup_sound cl_29541 [cl_6318,cl_29350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6318 v h) (hints_cons _ _ _ (der_29350 v h) (by intro d hd; cases hd)))
def cl_29542 : CNF.NClause := [(49,false),(18,true),(65,false),(73,false),(77,true),(86,true),(91,false)]
theorem der_29542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29542 :=
  CNF.rup_sound cl_29542 [cl_6326,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6326 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_29543 : CNF.NClause := [(49,false),(18,true),(65,false),(73,true),(77,true),(86,true),(91,false)]
theorem der_29543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29543 :=
  CNF.rup_sound cl_29543 [cl_6334,cl_29398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6334 v h) (hints_cons _ _ _ (der_29398 v h) (by intro d hd; cases hd)))
def cl_29544 : CNF.NClause := [(49,false),(18,true),(65,false),(73,false),(77,false),(86,false),(91,true)]
theorem der_29544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29544 :=
  CNF.rup_sound cl_29544 [cl_6342,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6342 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29545 : CNF.NClause := [(49,false),(18,true),(65,false),(73,true),(77,false),(86,false),(91,true)]
theorem der_29545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29545 :=
  CNF.rup_sound cl_29545 [cl_6350,cl_29399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6350 v h) (hints_cons _ _ _ (der_29399 v h) (by intro d hd; cases hd)))
def cl_29546 : CNF.NClause := [(49,false),(69,true),(18,true),(73,false),(77,true),(86,false),(91,true)]
theorem der_29546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29546 :=
  CNF.rup_sound cl_29546 [cl_6358,cl_29360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6358 v h) (hints_cons _ _ _ (der_29360 v h) (by intro d hd; cases hd)))
def cl_29547 : CNF.NClause := [(49,false),(18,true),(65,false),(73,true),(77,true),(86,false),(91,true)]
theorem der_29547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29547 :=
  CNF.rup_sound cl_29547 [cl_6366,cl_29400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6366 v h) (hints_cons _ _ _ (der_29400 v h) (by intro d hd; cases hd)))
def cl_29548 : CNF.NClause := [(49,false),(18,true),(65,false),(73,false),(77,false),(86,true),(91,true)]
theorem der_29548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29548 :=
  CNF.rup_sound cl_29548 [cl_6374,cl_29054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6374 v h) (hints_cons _ _ _ (der_29054 v h) (by intro d hd; cases hd)))
def cl_29549 : CNF.NClause := [(49,false),(69,true),(65,false),(73,true),(77,false),(86,true),(91,true)]
theorem der_29549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29549 :=
  CNF.rup_sound cl_29549 [cl_6382,cl_29533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6382 v h) (hints_cons _ _ _ (der_29533 v h) (by intro d hd; cases hd)))
def cl_29550 : CNF.NClause := [(49,false),(18,true),(65,false),(73,false),(77,true),(86,true),(91,true)]
theorem der_29550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29550 :=
  CNF.rup_sound cl_29550 [cl_6390,cl_29050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6390 v h) (hints_cons _ _ _ (der_29050 v h) (by intro d hd; cases hd)))
def cl_29551 : CNF.NClause := [(49,false),(69,true),(18,true),(73,true),(77,true),(86,true),(91,true)]
theorem der_29551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29551 :=
  CNF.rup_sound cl_29551 [cl_6398,cl_29370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6398 v h) (hints_cons _ _ _ (der_29370 v h) (by intro d hd; cases hd)))
def cl_29552 : CNF.NClause := [(52,false),(66,true),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem der_29552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29552 :=
  CNF.rup_sound cl_29552 [cl_6663,cl_29213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6663 v h) (hints_cons _ _ _ (der_29213 v h) (by intro d hd; cases hd)))
def cl_29553 : CNF.NClause := [(52,false),(66,true),(21,false),(79,false),(73,true),(85,false),(88,false)]
theorem der_29553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29553 :=
  CNF.rup_sound cl_29553 [cl_6671,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6671 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29554 : CNF.NClause := [(52,false),(21,false),(66,true),(85,false),(67,true),(73,false),(88,false)]
theorem der_29554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29554 :=
  CNF.rup_sound cl_29554 [cl_6679,cl_29552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6679 v h) (hints_cons _ _ _ (der_29552 v h) (by intro d hd; cases hd)))
def cl_29555 : CNF.NClause := [(52,false),(79,true),(21,false),(66,true),(73,true),(85,false),(88,false)]
theorem der_29555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29555 :=
  CNF.rup_sound cl_29555 [cl_6687,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6687 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29556 : CNF.NClause := [(52,false),(66,true),(67,true),(88,false),(79,false),(73,false),(85,true)]
theorem der_29556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29556 :=
  CNF.rup_sound cl_29556 [cl_6695,cl_29221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6695 v h) (hints_cons _ _ _ (der_29221 v h) (by intro d hd; cases hd)))
def cl_29557 : CNF.NClause := [(52,false),(88,false),(21,false),(66,true),(73,true),(79,false),(85,true)]
theorem der_29557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29557 :=
  CNF.rup_sound cl_29557 [cl_6703,cl_29193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6703 v h) (hints_cons _ _ _ (der_29193 v h) (by intro d hd; cases hd)))
def cl_29560 : CNF.NClause := [(52,false),(66,true),(21,false),(88,true),(79,false),(85,false),(73,false)]
theorem der_29560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29560 :=
  CNF.rup_sound cl_29560 [cl_6727,cl_29228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6727 v h) (hints_cons _ _ _ (der_29228 v h) (by intro d hd; cases hd)))
def cl_29561 : CNF.NClause := [(52,false),(88,true),(21,false),(66,true),(73,true),(85,false),(79,false)]
theorem der_29561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29561 :=
  CNF.rup_sound cl_29561 [cl_6735,cl_29197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6735 v h) (hints_cons _ _ _ (der_29197 v h) (by intro d hd; cases hd)))
def cl_29563 : CNF.NClause := [(52,false),(79,true),(21,false),(66,true),(73,true),(85,false),(88,true)]
theorem der_29563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29563 :=
  CNF.rup_sound cl_29563 [cl_6751,cl_29199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6751 v h) (hints_cons _ _ _ (der_29199 v h) (by intro d hd; cases hd)))
def cl_29564 : CNF.NClause := [(52,false),(66,true),(21,false),(85,true),(67,true),(79,false),(73,false)]
theorem der_29564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29564 :=
  CNF.rup_sound cl_29564 [cl_6759,cl_29556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6759 v h) (hints_cons _ _ _ (der_29556 v h) (by intro d hd; cases hd)))
def cl_29565 : CNF.NClause := [(52,false),(88,true),(21,false),(66,true),(73,true),(79,false),(85,true)]
theorem der_29565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29565 :=
  CNF.rup_sound cl_29565 [cl_6767,cl_29201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6767 v h) (hints_cons _ _ _ (der_29201 v h) (by intro d hd; cases hd)))
def cl_29568 : CNF.NClause := [(53,false),(75,true),(78,false),(22,false),(64,false),(86,false),(90,false)]
theorem der_29568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29568 :=
  CNF.rup_sound cl_29568 [cl_6797,cl_29452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6797 v h) (hints_cons _ _ _ (der_29452 v h) (by intro d hd; cases hd)))
def cl_29569 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,false),(86,false),(90,false)]
theorem der_29569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29569 :=
  CNF.rup_sound cl_29569 [cl_6805,cl_29082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6805 v h) (hints_cons _ _ _ (der_29082 v h) (by intro d hd; cases hd)))
def cl_29570 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,true),(86,false),(90,false)]
theorem der_29570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29570 :=
  CNF.rup_sound cl_29570 [cl_6813,cl_29453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6813 v h) (hints_cons _ _ _ (der_29453 v h) (by intro d hd; cases hd)))
def cl_29571 : CNF.NClause := [(53,false),(86,true),(64,false),(22,false),(75,false),(78,false),(90,false)]
theorem der_29571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29571 :=
  CNF.rup_sound cl_29571 [cl_6821,cl_29042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6821 v h) (hints_cons _ _ _ (der_29042 v h) (by intro d hd; cases hd)))
def cl_29572 : CNF.NClause := [(53,false),(75,true),(64,false),(22,false),(78,false),(86,true),(90,false)]
theorem der_29572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29572 :=
  CNF.rup_sound cl_29572 [cl_6829,cl_29454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6829 v h) (hints_cons _ _ _ (der_29454 v h) (by intro d hd; cases hd)))
def cl_29573 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,false),(86,true),(90,false)]
theorem der_29573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29573 :=
  CNF.rup_sound cl_29573 [cl_6837,cl_29083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6837 v h) (hints_cons _ _ _ (der_29083 v h) (by intro d hd; cases hd)))
def cl_29574 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,true),(86,true),(90,false)]
theorem der_29574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29574 :=
  CNF.rup_sound cl_29574 [cl_6845,cl_29455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6845 v h) (hints_cons _ _ _ (der_29455 v h) (by intro d hd; cases hd)))
def cl_29575 : CNF.NClause := [(53,false),(90,true),(64,false),(22,false),(75,false),(78,false),(86,false)]
theorem der_29575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29575 :=
  CNF.rup_sound cl_29575 [cl_6853,cl_29039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6853 v h) (hints_cons _ _ _ (der_29039 v h) (by intro d hd; cases hd)))
def cl_29576 : CNF.NClause := [(53,false),(75,true),(64,false),(22,false),(78,false),(86,false),(90,true)]
theorem der_29576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29576 :=
  CNF.rup_sound cl_29576 [cl_6861,cl_29456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6861 v h) (hints_cons _ _ _ (der_29456 v h) (by intro d hd; cases hd)))
def cl_29577 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,false),(86,false),(90,true)]
theorem der_29577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29577 :=
  CNF.rup_sound cl_29577 [cl_6869,cl_29084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6869 v h) (hints_cons _ _ _ (der_29084 v h) (by intro d hd; cases hd)))
def cl_29578 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,true),(86,false),(90,true)]
theorem der_29578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29578 :=
  CNF.rup_sound cl_29578 [cl_6877,cl_29457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6877 v h) (hints_cons _ _ _ (der_29457 v h) (by intro d hd; cases hd)))
def cl_29579 : CNF.NClause := [(53,false),(90,true),(64,false),(22,false),(75,false),(78,false),(86,true)]
theorem der_29579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29579 :=
  CNF.rup_sound cl_29579 [cl_6885,cl_29043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6885 v h) (hints_cons _ _ _ (der_29043 v h) (by intro d hd; cases hd)))
def cl_29580 : CNF.NClause := [(53,false),(90,true),(64,false),(22,false),(75,true),(67,true),(78,false)]
theorem der_29580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29580 :=
  CNF.rup_sound cl_29580 [cl_6893,cl_29576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6893 v h) (hints_cons _ _ _ (der_29576 v h) (by intro d hd; cases hd)))
def cl_29581 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,false),(86,true),(90,true)]
theorem der_29581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29581 :=
  CNF.rup_sound cl_29581 [cl_6901,cl_29085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6901 v h) (hints_cons _ _ _ (der_29085 v h) (by intro d hd; cases hd)))
def cl_29582 : CNF.NClause := [(53,false),(78,true),(64,false),(22,false),(75,true),(67,true),(86,true)]
theorem der_29582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29582 :=
  CNF.rup_sound cl_29582 [cl_6909,cl_29574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6909 v h) (hints_cons _ _ _ (der_29574 v h) (by intro d hd; cases hd)))
def cl_29583 : CNF.NClause := [(52,false),(67,true),(66,false),(85,false),(73,false),(79,false),(88,false)]
theorem der_29583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29583 :=
  CNF.rup_sound cl_29583 [cl_6661,cl_26350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6661 v h) (hints_cons _ _ _ (der_26350 v h) (by intro d hd; cases hd)))
def cl_29584 : CNF.NClause := [(52,false),(21,false),(79,false),(66,false),(73,true),(85,false),(88,false)]
theorem der_29584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29584 :=
  CNF.rup_sound cl_29584 [cl_6669,cl_29387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6669 v h) (hints_cons _ _ _ (der_29387 v h) (by intro d hd; cases hd)))
def cl_29585 : CNF.NClause := [(52,false),(79,true),(21,false),(66,false),(73,false),(85,false),(88,false)]
theorem der_29585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29585 :=
  CNF.rup_sound cl_29585 [cl_6677,cl_29074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6677 v h) (hints_cons _ _ _ (der_29074 v h) (by intro d hd; cases hd)))
def cl_29586 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(85,false),(88,false)]
theorem der_29586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29586 :=
  CNF.rup_sound cl_29586 [cl_6685,cl_29584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6685 v h) (hints_cons _ _ _ (der_29584 v h) (by intro d hd; cases hd)))
def cl_29587 : CNF.NClause := [(52,false),(85,true),(21,false),(66,false),(73,false),(79,false),(88,false)]
theorem der_29587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29587 :=
  CNF.rup_sound cl_29587 [cl_6693,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6693 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29591 : CNF.NClause := [(52,false),(88,true),(85,false),(73,false),(79,false),(66,false),(67,true)]
theorem der_29591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29591 :=
  CNF.rup_sound cl_29591 [cl_6725,cl_26360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6725 v h) (hints_cons _ _ _ (der_26360 v h) (by intro d hd; cases hd)))
def cl_29592 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(85,false),(79,false)]
theorem der_29592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29592 :=
  CNF.rup_sound cl_29592 [cl_6733,cl_29586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6733 v h) (hints_cons _ _ _ (der_29586 v h) (by intro d hd; cases hd)))
def cl_29593 : CNF.NClause := [(52,false),(79,true),(21,false),(66,false),(73,false),(85,false),(88,true)]
theorem der_29593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29593 :=
  CNF.rup_sound cl_29593 [cl_6741,cl_29068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6741 v h) (hints_cons _ _ _ (der_29068 v h) (by intro d hd; cases hd)))
def cl_29595 : CNF.NClause := [(52,false),(85,true),(21,false),(88,true),(73,false),(79,false),(66,false)]
theorem der_29595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29595 :=
  CNF.rup_sound cl_29595 [cl_6757,cl_29069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6757 v h) (hints_cons _ _ _ (der_29069 v h) (by intro d hd; cases hd)))
def cl_29596 : CNF.NClause := [(52,false),(88,true),(21,false),(66,false),(73,true),(79,false),(85,true)]
theorem der_29596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29596 :=
  CNF.rup_sound cl_29596 [cl_6765,cl_29385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6765 v h) (hints_cons _ _ _ (der_29385 v h) (by intro d hd; cases hd)))
def cl_29599 : CNF.NClause := [(53,false),(75,true),(22,true),(64,true),(78,false),(86,false),(90,false)]
theorem der_29599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29599 :=
  CNF.rup_sound cl_29599 [cl_6800,cl_29468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6800 v h) (hints_cons _ _ _ (der_29468 v h) (by intro d hd; cases hd)))
def cl_29600 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(75,false),(86,false),(90,false)]
theorem der_29600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29600 :=
  CNF.rup_sound cl_29600 [cl_6808,cl_29090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6808 v h) (hints_cons _ _ _ (der_29090 v h) (by intro d hd; cases hd)))
def cl_29601 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(75,true),(86,false),(90,false)]
theorem der_29601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29601 :=
  CNF.rup_sound cl_29601 [cl_6816,cl_29469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6816 v h) (hints_cons _ _ _ (der_29469 v h) (by intro d hd; cases hd)))
def cl_29602 : CNF.NClause := [(53,false),(22,true),(64,true),(75,false),(78,false),(86,true),(90,false)]
theorem der_29602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29602 :=
  CNF.rup_sound cl_29602 [cl_6824,cl_29047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6824 v h) (hints_cons _ _ _ (der_29047 v h) (by intro d hd; cases hd)))
def cl_29603 : CNF.NClause := [(53,false),(75,true),(22,true),(64,true),(78,false),(86,true),(90,false)]
theorem der_29603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29603 :=
  CNF.rup_sound cl_29603 [cl_6832,cl_29470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6832 v h) (hints_cons _ _ _ (der_29470 v h) (by intro d hd; cases hd)))
def cl_29604 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(75,false),(86,true),(90,false)]
theorem der_29604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29604 :=
  CNF.rup_sound cl_29604 [cl_6840,cl_29091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6840 v h) (hints_cons _ _ _ (der_29091 v h) (by intro d hd; cases hd)))
def cl_29605 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(75,true),(86,true),(90,false)]
theorem der_29605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29605 :=
  CNF.rup_sound cl_29605 [cl_6848,cl_29471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6848 v h) (hints_cons _ _ _ (der_29471 v h) (by intro d hd; cases hd)))
def cl_29606 : CNF.NClause := [(53,false),(90,true),(22,true),(64,true),(75,false),(78,false),(86,false)]
theorem der_29606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29606 :=
  CNF.rup_sound cl_29606 [cl_6856,cl_29040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6856 v h) (hints_cons _ _ _ (der_29040 v h) (by intro d hd; cases hd)))
def cl_29607 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(78,false),(86,false),(90,true)]
theorem der_29607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29607 :=
  CNF.rup_sound cl_29607 [cl_6864,cl_29606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6864 v h) (hints_cons _ _ _ (der_29606 v h) (by intro d hd; cases hd)))
def cl_29608 : CNF.NClause := [(53,false),(22,true),(64,true),(75,false),(67,true),(86,false),(90,true)]
theorem der_29608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29608 :=
  CNF.rup_sound cl_29608 [cl_6872,cl_29606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6872 v h) (hints_cons _ _ _ (der_29606 v h) (by intro d hd; cases hd)))
def cl_29609 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(75,true),(86,false),(90,true)]
theorem der_29609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29609 :=
  CNF.rup_sound cl_29609 [cl_6880,cl_29473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6880 v h) (hints_cons _ _ _ (der_29473 v h) (by intro d hd; cases hd)))
def cl_29610 : CNF.NClause := [(53,false),(67,true),(22,true),(64,true),(75,false),(78,false),(90,true)]
theorem der_29610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29610 :=
  CNF.rup_sound cl_29610 [cl_6888,cl_29606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6888 v h) (hints_cons _ _ _ (der_29606 v h) (by intro d hd; cases hd)))
def cl_29611 : CNF.NClause := [(53,false),(75,true),(22,true),(64,true),(78,false),(86,true),(90,true)]
theorem der_29611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29611 :=
  CNF.rup_sound cl_29611 [cl_6896,cl_29474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6896 v h) (hints_cons _ _ _ (der_29474 v h) (by intro d hd; cases hd)))
def cl_29612 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(75,false),(67,true),(86,true)]
theorem der_29612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29612 :=
  CNF.rup_sound cl_29612 [cl_6904,cl_29604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6904 v h) (hints_cons _ _ _ (der_29604 v h) (by intro d hd; cases hd)))
def cl_29613 : CNF.NClause := [(53,false),(78,true),(22,true),(64,true),(75,true),(86,true),(90,true)]
theorem der_29613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29613 :=
  CNF.rup_sound cl_29613 [cl_6912,cl_29475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6912 v h) (hints_cons _ _ _ (der_29475 v h) (by intro d hd; cases hd)))
def cl_29614 : CNF.NClause := [(53,false),(22,true),(78,false),(64,false),(75,false),(90,false),(86,false)]
theorem der_29614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29614 :=
  CNF.rup_sound cl_29614 [cl_6790,cl_6786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6790 v h) (hints_cons _ _ _ (inp_6786 v h) (by intro d hd; cases hd)))
def cl_29615 : CNF.NClause := [(53,false),(75,true),(22,true),(64,false),(78,false),(86,false),(90,false)]
theorem der_29615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29615 :=
  CNF.rup_sound cl_29615 [cl_6798,cl_29452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6798 v h) (hints_cons _ _ _ (der_29452 v h) (by intro d hd; cases hd)))
def cl_29616 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(75,false),(86,false),(90,false)]
theorem der_29616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29616 :=
  CNF.rup_sound cl_29616 [cl_6806,cl_29082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6806 v h) (hints_cons _ _ _ (der_29082 v h) (by intro d hd; cases hd)))
def cl_29617 : CNF.NClause := [(53,false),(78,true),(64,false),(75,true),(67,true),(86,false),(90,false)]
theorem der_29617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29617 :=
  CNF.rup_sound cl_29617 [cl_6814,cl_29570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6814 v h) (hints_cons _ _ _ (der_29570 v h) (by intro d hd; cases hd)))
def cl_29618 : CNF.NClause := [(53,false),(22,true),(64,false),(75,false),(78,false),(86,true),(90,false)]
theorem der_29618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29618 :=
  CNF.rup_sound cl_29618 [cl_6822,cl_29042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6822 v h) (hints_cons _ _ _ (der_29042 v h) (by intro d hd; cases hd)))
def cl_29619 : CNF.NClause := [(53,false),(67,true),(64,false),(75,true),(78,false),(86,true),(90,false)]
theorem der_29619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29619 :=
  CNF.rup_sound cl_29619 [cl_6830,cl_29572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6830 v h) (hints_cons _ _ _ (der_29572 v h) (by intro d hd; cases hd)))
def cl_29620 : CNF.NClause := [(53,false),(78,true),(22,true),(75,false),(67,true),(86,true),(90,false)]
theorem der_29620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29620 :=
  CNF.rup_sound cl_29620 [cl_6838,cl_29604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6838 v h) (hints_cons _ _ _ (der_29604 v h) (by intro d hd; cases hd)))
def cl_29621 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(75,true),(86,true),(90,false)]
theorem der_29621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29621 :=
  CNF.rup_sound cl_29621 [cl_6846,cl_29455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6846 v h) (hints_cons _ _ _ (der_29455 v h) (by intro d hd; cases hd)))
def cl_29622 : CNF.NClause := [(53,false),(90,true),(22,true),(64,false),(75,false),(86,false),(78,false)]
theorem der_29622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29622 :=
  CNF.rup_sound cl_29622 [cl_6854,cl_29039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6854 v h) (hints_cons _ _ _ (der_29039 v h) (by intro d hd; cases hd)))
def cl_29623 : CNF.NClause := [(53,false),(75,true),(64,false),(90,true),(78,false),(86,false),(67,true)]
theorem der_29623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29623 :=
  CNF.rup_sound cl_29623 [cl_6862,cl_29576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6862 v h) (hints_cons _ _ _ (der_29576 v h) (by intro d hd; cases hd)))
def cl_29624 : CNF.NClause := [(53,false),(78,true),(22,true),(75,false),(67,true),(86,false),(90,true)]
theorem der_29624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29624 :=
  CNF.rup_sound cl_29624 [cl_6870,cl_29608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6870 v h) (hints_cons _ _ _ (der_29608 v h) (by intro d hd; cases hd)))
def cl_29625 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(75,true),(86,false),(90,true)]
theorem der_29625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29625 :=
  CNF.rup_sound cl_29625 [cl_6878,cl_29457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6878 v h) (hints_cons _ _ _ (der_29457 v h) (by intro d hd; cases hd)))
def cl_29626 : CNF.NClause := [(53,false),(67,true),(64,false),(75,false),(78,false),(86,true),(90,true)]
theorem der_29626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29626 :=
  CNF.rup_sound cl_29626 [cl_6886,cl_29579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6886 v h) (hints_cons _ _ _ (der_29579 v h) (by intro d hd; cases hd)))
def cl_29627 : CNF.NClause := [(53,false),(67,true),(64,false),(75,true),(78,false),(86,true),(90,true)]
theorem der_29627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29627 :=
  CNF.rup_sound cl_29627 [cl_6894,cl_29580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6894 v h) (hints_cons _ _ _ (der_29580 v h) (by intro d hd; cases hd)))
def cl_29628 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(75,false),(86,true),(90,true)]
theorem der_29628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29628 :=
  CNF.rup_sound cl_29628 [cl_6902,cl_29085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6902 v h) (hints_cons _ _ _ (der_29085 v h) (by intro d hd; cases hd)))
def cl_29629 : CNF.NClause := [(53,false),(78,true),(64,false),(75,true),(67,true),(86,true),(90,true)]
theorem der_29629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29629 :=
  CNF.rup_sound cl_29629 [cl_6910,cl_29582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6910 v h) (hints_cons _ _ _ (der_29582 v h) (by intro d hd; cases hd)))
def cl_29630 : CNF.NClause := [(45,false),(70,true),(14,false),(86,false),(72,false),(89,false),(79,false)]
theorem der_29630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29630 :=
  CNF.rup_sound cl_29630 [cl_5767,cl_29094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5767 v h) (hints_cons _ _ _ (der_29094 v h) (by intro d hd; cases hd)))
def cl_29631 : CNF.NClause := [(45,false),(72,true),(70,false),(63,true),(79,false),(86,false),(89,false)]
theorem der_29631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29631 :=
  CNF.rup_sound cl_29631 [cl_5771,cl_29492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5771 v h) (hints_cons _ _ _ (der_29492 v h) (by intro d hd; cases hd)))
def cl_29632 : CNF.NClause := [(45,false),(72,true),(14,false),(70,true),(79,false),(86,false),(89,false)]
theorem der_29632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29632 :=
  CNF.rup_sound cl_29632 [cl_5775,cl_29103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5775 v h) (hints_cons _ _ _ (der_29103 v h) (by intro d hd; cases hd)))
def cl_29633 : CNF.NClause := [(45,false),(79,true),(14,false),(70,false),(72,false),(86,false),(89,false)]
theorem der_29633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29633 :=
  CNF.rup_sound cl_29633 [cl_5779,cl_29078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5779 v h) (hints_cons _ _ _ (der_29078 v h) (by intro d hd; cases hd)))
def cl_29634 : CNF.NClause := [(45,false),(79,true),(63,true),(70,true),(72,false),(86,false),(89,false)]
theorem der_29634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29634 :=
  CNF.rup_sound cl_29634 [cl_5783,cl_29120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5783 v h) (hints_cons _ _ _ (der_29120 v h) (by intro d hd; cases hd)))
def cl_29635 : CNF.NClause := [(45,false),(14,false),(70,false),(63,true),(72,true),(86,false),(89,false)]
theorem der_29635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29635 :=
  CNF.rup_sound cl_29635 [cl_5787,cl_29631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5787 v h) (hints_cons _ _ _ (der_29631 v h) (by intro d hd; cases hd)))
def cl_29636 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(79,true),(86,false),(89,false)]
theorem der_29636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29636 :=
  CNF.rup_sound cl_29636 [cl_5791,cl_29634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5791 v h) (hints_cons _ _ _ (der_29634 v h) (by intro d hd; cases hd)))
def cl_29637 : CNF.NClause := [(45,false),(14,false),(70,false),(79,false),(72,false),(86,true),(89,false)]
theorem der_29637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29637 :=
  CNF.rup_sound cl_29637 [cl_5795,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5795 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29638 : CNF.NClause := [(45,false),(63,true),(14,false),(72,false),(79,false),(86,true),(89,false)]
theorem der_29638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29638 :=
  CNF.rup_sound cl_29638 [cl_5799,cl_29637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5799 v h) (hints_cons _ _ _ (der_29637 v h) (by intro d hd; cases hd)))
def cl_29639 : CNF.NClause := [(45,false),(14,false),(70,false),(63,true),(79,false),(72,true),(89,false)]
theorem der_29639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29639 :=
  CNF.rup_sound cl_29639 [cl_5803,cl_29631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5803 v h) (hints_cons _ _ _ (der_29631 v h) (by intro d hd; cases hd)))
def cl_29640 : CNF.NClause := [(45,false),(72,true),(63,true),(70,true),(79,false),(86,true),(89,false)]
theorem der_29640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29640 :=
  CNF.rup_sound cl_29640 [cl_5807,cl_29494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5807 v h) (hints_cons _ _ _ (der_29494 v h) (by intro d hd; cases hd)))
def cl_29641 : CNF.NClause := [(45,false),(14,false),(70,false),(72,false),(63,true),(86,true),(89,false)]
theorem der_29641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29641 :=
  CNF.rup_sound cl_29641 [cl_5811,cl_29637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5811 v h) (hints_cons _ _ _ (der_29637 v h) (by intro d hd; cases hd)))
def cl_29642 : CNF.NClause := [(45,false),(79,true),(14,false),(70,true),(72,false),(86,true),(89,false)]
theorem der_29642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29642 :=
  CNF.rup_sound cl_29642 [cl_5815,cl_29100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5815 v h) (hints_cons _ _ _ (der_29100 v h) (by intro d hd; cases hd)))
def cl_29643 : CNF.NClause := [(45,false),(79,true),(70,false),(63,true),(72,true),(86,true),(89,false)]
theorem der_29643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29643 :=
  CNF.rup_sound cl_29643 [cl_5819,cl_29495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5819 v h) (hints_cons _ _ _ (der_29495 v h) (by intro d hd; cases hd)))
def cl_29644 : CNF.NClause := [(45,false),(72,true),(63,true),(70,true),(79,true),(86,true),(89,false)]
theorem der_29644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29644 :=
  CNF.rup_sound cl_29644 [cl_5823,cl_29495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5823 v h) (hints_cons _ _ _ (der_29495 v h) (by intro d hd; cases hd)))
def cl_29645 : CNF.NClause := [(45,false),(14,false),(72,false),(70,false),(89,true),(86,false),(79,false)]
theorem der_29645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29645 :=
  CNF.rup_sound cl_29645 [cl_5827,cl_29403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5827 v h) (hints_cons _ _ _ (der_29403 v h) (by intro d hd; cases hd)))
def cl_29646 : CNF.NClause := [(45,false),(63,true),(86,false),(79,false),(89,true),(70,true),(72,false)]
theorem der_29646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29646 :=
  CNF.rup_sound cl_29646 [cl_5831,cl_29118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5831 v h) (hints_cons _ _ _ (der_29118 v h) (by intro d hd; cases hd)))
def cl_29647 : CNF.NClause := [(45,false),(89,true),(14,false),(79,false),(70,false),(86,false),(72,true)]
theorem der_29647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29647 :=
  CNF.rup_sound cl_29647 [cl_5835,cl_29488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5835 v h) (hints_cons _ _ _ (der_29488 v h) (by intro d hd; cases hd)))
def cl_29648 : CNF.NClause := [(45,false),(72,true),(14,false),(70,true),(79,false),(86,false),(89,true)]
theorem der_29648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29648 :=
  CNF.rup_sound cl_29648 [cl_5839,cl_29103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5839 v h) (hints_cons _ _ _ (der_29103 v h) (by intro d hd; cases hd)))
def cl_29649 : CNF.NClause := [(45,false),(79,true),(14,false),(70,false),(72,false),(86,false),(89,true)]
theorem der_29649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29649 :=
  CNF.rup_sound cl_29649 [cl_5843,cl_29071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5843 v h) (hints_cons _ _ _ (der_29071 v h) (by intro d hd; cases hd)))
def cl_29650 : CNF.NClause := [(45,false),(79,true),(63,true),(70,true),(72,false),(86,false),(89,true)]
theorem der_29650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29650 :=
  CNF.rup_sound cl_29650 [cl_5847,cl_29120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5847 v h) (hints_cons _ _ _ (der_29120 v h) (by intro d hd; cases hd)))
def cl_29653 : CNF.NClause := [(45,false),(63,true),(14,false),(70,false),(79,false),(72,false),(86,true)]
theorem der_29653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29653 :=
  CNF.rup_sound cl_29653 [cl_5859,cl_29637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5859 v h) (hints_cons _ _ _ (der_29637 v h) (by intro d hd; cases hd)))
def cl_29654 : CNF.NClause := [(45,false),(14,false),(72,false),(70,true),(79,false),(86,true),(89,true)]
theorem der_29654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29654 :=
  CNF.rup_sound cl_29654 [cl_5863,cl_29106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5863 v h) (hints_cons _ _ _ (der_29106 v h) (by intro d hd; cases hd)))
def cl_29655 : CNF.NClause := [(45,false),(86,true),(14,false),(70,false),(79,false),(72,true),(89,true)]
theorem der_29655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29655 :=
  CNF.rup_sound cl_29655 [cl_5867,cl_29490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5867 v h) (hints_cons _ _ _ (der_29490 v h) (by intro d hd; cases hd)))
def cl_29656 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(79,false),(86,true),(89,true)]
theorem der_29656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29656 :=
  CNF.rup_sound cl_29656 [cl_5871,cl_29654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5871 v h) (hints_cons _ _ _ (der_29654 v h) (by intro d hd; cases hd)))
def cl_29658 : CNF.NClause := [(45,false),(79,true),(63,true),(70,true),(72,false),(86,true),(89,true)]
theorem der_29658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29658 :=
  CNF.rup_sound cl_29658 [cl_5879,cl_29124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5879 v h) (hints_cons _ _ _ (der_29124 v h) (by intro d hd; cases hd)))
def cl_29661 : CNF.NClause := [(45,false),(14,true),(72,false),(86,false),(70,false),(89,true),(79,false)]
theorem der_29661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29661 :=
  CNF.rup_sound cl_29661 [cl_5828,cl_29408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5828 v h) (hints_cons _ _ _ (der_29408 v h) (by intro d hd; cases hd)))
def cl_29662 : CNF.NClause := [(45,false),(63,true),(14,true),(70,false),(79,false),(86,false),(72,true)]
theorem der_29662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29662 :=
  CNF.rup_sound cl_29662 [cl_5836,cl_29631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5836 v h) (hints_cons _ _ _ (der_29631 v h) (by intro d hd; cases hd)))
def cl_29663 : CNF.NClause := [(45,false),(79,true),(14,true),(63,true),(72,false),(86,false),(89,true)]
theorem der_29663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29663 :=
  CNF.rup_sound cl_29663 [cl_5844,cl_29120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5844 v h) (hints_cons _ _ _ (der_29120 v h) (by intro d hd; cases hd)))
def cl_29664 : CNF.NClause := [(45,false),(79,true),(14,true),(70,false),(72,true),(86,false),(89,true)]
theorem der_29664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29664 :=
  CNF.rup_sound cl_29664 [cl_5852,cl_29509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5852 v h) (hints_cons _ _ _ (der_29509 v h) (by intro d hd; cases hd)))
def cl_29665 : CNF.NClause := [(45,false),(63,true),(14,true),(79,false),(72,false),(86,true),(89,true)]
theorem der_29665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29665 :=
  CNF.rup_sound cl_29665 [cl_5860,cl_29122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5860 v h) (hints_cons _ _ _ (der_29122 v h) (by intro d hd; cases hd)))
def cl_29666 : CNF.NClause := [(45,false),(14,true),(70,false),(79,false),(72,true),(86,true),(89,true)]
theorem der_29666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29666 :=
  CNF.rup_sound cl_29666 [cl_5868,cl_29510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5868 v h) (hints_cons _ _ _ (der_29510 v h) (by intro d hd; cases hd)))
def cl_29667 : CNF.NClause := [(45,false),(79,true),(14,true),(70,false),(72,false),(86,true),(89,true)]
theorem der_29667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29667 :=
  CNF.rup_sound cl_29667 [cl_5876,cl_29081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5876 v h) (hints_cons _ _ _ (der_29081 v h) (by intro d hd; cases hd)))
def cl_29668 : CNF.NClause := [(45,false),(79,true),(14,true),(70,false),(63,true),(72,true),(86,true)]
theorem der_29668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29668 :=
  CNF.rup_sound cl_29668 [cl_5884,cl_29495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5884 v h) (hints_cons _ _ _ (der_29495 v h) (by intro d hd; cases hd)))
def cl_29669 : CNF.NClause := [(45,false),(14,true),(89,false),(72,false),(70,false),(79,false),(86,false)]
theorem der_29669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29669 :=
  CNF.rup_sound cl_29669 [cl_5764,cl_29408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5764 v h) (hints_cons _ _ _ (der_29408 v h) (by intro d hd; cases hd)))
def cl_29670 : CNF.NClause := [(53,false),(67,false),(22,true),(75,false),(86,false),(64,true),(78,false)]
theorem der_29670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29670 :=
  CNF.rup_sound cl_29670 [cl_6788,cl_29606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6788 v h) (hints_cons _ _ _ (der_29606 v h) (by intro d hd; cases hd)))
def cl_29671 : CNF.NClause := [(53,false),(67,true),(90,false),(75,false),(86,false),(64,true),(78,false)]
theorem der_29671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29671 :=
  CNF.rup_sound cl_29671 [cl_6791,cl_6792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6791 v h) (hints_cons _ _ _ (inp_6792 v h) (by intro d hd; cases hd)))
def cl_29672 : CNF.NClause := [(53,false),(75,true),(22,false),(67,false),(78,false),(86,false),(90,false)]
theorem der_29672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29672 :=
  CNF.rup_sound cl_29672 [cl_6795,cl_29452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6795 v h) (hints_cons _ _ _ (der_29452 v h) (by intro d hd; cases hd)))
def cl_29673 : CNF.NClause := [(53,false),(75,true),(64,true),(67,true),(78,false),(86,false),(90,false)]
theorem der_29673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29673 :=
  CNF.rup_sound cl_29673 [cl_6799,cl_29599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6799 v h) (hints_cons _ _ _ (der_29599 v h) (by intro d hd; cases hd)))
def cl_29674 : CNF.NClause := [(53,false),(78,true),(22,false),(67,false),(75,false),(86,false),(90,false)]
theorem der_29674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29674 :=
  CNF.rup_sound cl_29674 [cl_6803,cl_29082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6803 v h) (hints_cons _ _ _ (der_29082 v h) (by intro d hd; cases hd)))
def cl_29675 : CNF.NClause := [(53,false),(78,true),(64,true),(75,false),(67,true),(86,false),(90,false)]
theorem der_29675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29675 :=
  CNF.rup_sound cl_29675 [cl_6807,cl_29600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6807 v h) (hints_cons _ _ _ (der_29600 v h) (by intro d hd; cases hd)))
def cl_29676 : CNF.NClause := [(53,false),(78,true),(64,true),(67,false),(75,true),(86,false),(90,false)]
theorem der_29676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29676 :=
  CNF.rup_sound cl_29676 [cl_6811,cl_29469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6811 v h) (hints_cons _ _ _ (der_29469 v h) (by intro d hd; cases hd)))
def cl_29677 : CNF.NClause := [(53,false),(78,true),(64,true),(67,true),(75,true),(86,false),(90,false)]
theorem der_29677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29677 :=
  CNF.rup_sound cl_29677 [cl_6815,cl_29601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6815 v h) (hints_cons _ _ _ (der_29601 v h) (by intro d hd; cases hd)))
def cl_29678 : CNF.NClause := [(53,false),(67,false),(22,false),(90,false),(75,false),(86,true),(78,false)]
theorem der_29678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29678 :=
  CNF.rup_sound cl_29678 [cl_6819,cl_29042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6819 v h) (hints_cons _ _ _ (der_29042 v h) (by intro d hd; cases hd)))
def cl_29679 : CNF.NClause := [(53,false),(67,true),(64,true),(75,false),(78,false),(86,true),(90,false)]
theorem der_29679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29679 :=
  CNF.rup_sound cl_29679 [cl_6823,cl_29602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6823 v h) (hints_cons _ _ _ (der_29602 v h) (by intro d hd; cases hd)))
def cl_29680 : CNF.NClause := [(53,false),(75,true),(64,true),(67,false),(78,false),(86,true),(90,false)]
theorem der_29680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29680 :=
  CNF.rup_sound cl_29680 [cl_6827,cl_29470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6827 v h) (hints_cons _ _ _ (der_29470 v h) (by intro d hd; cases hd)))
def cl_29681 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(78,false),(86,true),(90,false)]
theorem der_29681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29681 :=
  CNF.rup_sound cl_29681 [cl_6831,cl_29679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6831 v h) (hints_cons _ _ _ (der_29679 v h) (by intro d hd; cases hd)))
def cl_29682 : CNF.NClause := [(53,false),(78,true),(64,true),(67,false),(75,false),(86,true),(90,false)]
theorem der_29682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29682 :=
  CNF.rup_sound cl_29682 [cl_6835,cl_29604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6835 v h) (hints_cons _ _ _ (der_29604 v h) (by intro d hd; cases hd)))
def cl_29683 : CNF.NClause := [(53,false),(78,true),(64,true),(75,false),(67,true),(86,true),(90,false)]
theorem der_29683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29683 :=
  CNF.rup_sound cl_29683 [cl_6839,cl_29604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6839 v h) (hints_cons _ _ _ (der_29604 v h) (by intro d hd; cases hd)))
def cl_29684 : CNF.NClause := [(53,false),(78,true),(22,false),(67,false),(75,true),(86,true),(90,false)]
theorem der_29684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29684 :=
  CNF.rup_sound cl_29684 [cl_6843,cl_29455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6843 v h) (hints_cons _ _ _ (der_29455 v h) (by intro d hd; cases hd)))
def cl_29685 : CNF.NClause := [(53,false),(78,true),(22,false),(67,true),(75,true),(86,true),(90,false)]
theorem der_29685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29685 :=
  CNF.rup_sound cl_29685 [cl_6847,cl_29574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6847 v h) (hints_cons _ _ _ (der_29574 v h) (by intro d hd; cases hd)))
def cl_29686 : CNF.NClause := [(53,false),(90,true),(22,false),(86,false),(78,false),(75,false),(67,false)]
theorem der_29686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29686 :=
  CNF.rup_sound cl_29686 [cl_6851,cl_29039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6851 v h) (hints_cons _ _ _ (der_29039 v h) (by intro d hd; cases hd)))
def cl_29687 : CNF.NClause := [(53,false),(90,true),(64,true),(75,false),(78,false),(86,false),(67,true)]
theorem der_29687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29687 :=
  CNF.rup_sound cl_29687 [cl_6855,cl_29606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6855 v h) (hints_cons _ _ _ (der_29606 v h) (by intro d hd; cases hd)))
def cl_29688 : CNF.NClause := [(53,false),(75,true),(22,false),(67,false),(78,false),(86,false),(90,true)]
theorem der_29688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29688 :=
  CNF.rup_sound cl_29688 [cl_6859,cl_29576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6859 v h) (hints_cons _ _ _ (der_29576 v h) (by intro d hd; cases hd)))
def cl_29689 : CNF.NClause := [(53,false),(75,true),(22,false),(67,true),(78,false),(86,false),(90,true)]
theorem der_29689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29689 :=
  CNF.rup_sound cl_29689 [cl_6863,cl_29576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6863 v h) (hints_cons _ _ _ (der_29576 v h) (by intro d hd; cases hd)))
def cl_29690 : CNF.NClause := [(53,false),(78,true),(64,true),(67,false),(75,false),(86,false),(90,true)]
theorem der_29690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29690 :=
  CNF.rup_sound cl_29690 [cl_6867,cl_29092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6867 v h) (hints_cons _ _ _ (der_29092 v h) (by intro d hd; cases hd)))
def cl_29691 : CNF.NClause := [(53,false),(78,true),(64,true),(75,false),(67,true),(86,false),(90,true)]
theorem der_29691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29691 :=
  CNF.rup_sound cl_29691 [cl_6871,cl_29608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6871 v h) (hints_cons _ _ _ (der_29608 v h) (by intro d hd; cases hd)))
def cl_29692 : CNF.NClause := [(53,false),(78,true),(22,false),(67,false),(75,true),(86,false),(90,true)]
theorem der_29692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29692 :=
  CNF.rup_sound cl_29692 [cl_6875,cl_29457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6875 v h) (hints_cons _ _ _ (der_29457 v h) (by intro d hd; cases hd)))
def cl_29693 : CNF.NClause := [(53,false),(78,true),(22,false),(67,true),(75,true),(86,false),(90,true)]
theorem der_29693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29693 :=
  CNF.rup_sound cl_29693 [cl_6879,cl_29578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6879 v h) (hints_cons _ _ _ (der_29578 v h) (by intro d hd; cases hd)))
def cl_29694 : CNF.NClause := [(53,false),(90,true),(22,false),(64,true),(67,false),(75,false),(78,false)]
theorem der_29694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29694 :=
  CNF.rup_sound cl_29694 [cl_6883,cl_29686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6883 v h) (hints_cons _ _ _ (der_29686 v h) (by intro d hd; cases hd)))
def cl_29695 : CNF.NClause := [(53,false),(22,false),(64,true),(75,false),(78,false),(86,true),(90,true)]
theorem der_29695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29695 :=
  CNF.rup_sound cl_29695 [cl_6887,cl_29694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6887 v h) (hints_cons _ _ _ (der_29694 v h) (by intro d hd; cases hd)))
def cl_29698 : CNF.NClause := [(53,false),(78,true),(22,false),(67,false),(75,false),(86,true),(90,true)]
theorem der_29698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29698 :=
  CNF.rup_sound cl_29698 [cl_6899,cl_29085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6899 v h) (hints_cons _ _ _ (der_29085 v h) (by intro d hd; cases hd)))
def cl_29699 : CNF.NClause := [(53,false),(78,true),(22,false),(64,true),(75,false),(67,true),(86,true)]
theorem der_29699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29699 :=
  CNF.rup_sound cl_29699 [cl_6903,cl_29683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6903 v h) (hints_cons _ _ _ (der_29683 v h) (by intro d hd; cases hd)))
def cl_29765 : CNF.NClause := [(27,false),(62,true),(26,false)]
theorem der_29765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29765 :=
  CNF.rup_sound cl_29765 [cl_23183,cl_23176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23183 v h) (hints_cons _ _ _ (der_23176 v h) (by intro d hd; cases hd)))
def cl_29766 : CNF.NClause := [(12,false),(22,false),(64,true)]
theorem der_29766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29766 :=
  CNF.rup_sound cl_29766 [cl_23190,cl_23361,cl_23456,cl_23225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23190 v h) (hints_cons _ _ _ (der_23361 v h) (hints_cons _ _ _ (der_23456 v h) (hints_cons _ _ _ (der_23225 v h) (by intro d hd; cases hd)))))
def cl_29767 : CNF.NClause := [(87,false),(3,true),(1,true),(2,true)]
theorem der_29767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29767 :=
  CNF.rup_sound cl_29767 [cl_15908,cl_15907,cl_15909,cl_15742,cl_15910,cl_15274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15908 v h) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_15909 v h) (hints_cons _ _ _ (der_15742 v h) (hints_cons _ _ _ (der_15910 v h) (hints_cons _ _ _ (der_15274 v h) (by intro d hd; cases hd)))))))
def cl_29768 : CNF.NClause := [(87,false),(4,true),(1,true),(2,true)]
theorem der_29768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29768 :=
  CNF.rup_sound cl_29768 [cl_15768,cl_15767,cl_15770,cl_15661,cl_15769,cl_15278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_15278 v h) (by intro d hd; cases hd)))))))
def cl_29769 : CNF.NClause := [(87,false),(4,true),(3,true),(2,true)]
theorem der_29769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29769 :=
  CNF.rup_sound cl_29769 [cl_15768,cl_15769,cl_15770,cl_15661,cl_15767,cl_15281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15281 v h) (by intro d hd; cases hd)))))))
def cl_29770 : CNF.NClause := [(22,false),(17,false),(64,true),(2,true)]
theorem der_29770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29770 :=
  CNF.rup_sound cl_29770 [cl_29766,cl_15054,cl_23360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29766 v h) (hints_cons _ _ _ (der_15054 v h) (hints_cons _ _ _ (der_23360 v h) (by intro d hd; cases hd))))
def cl_29771 : CNF.NClause := [(16,false),(66,true),(1,false),(21,true)]
theorem der_29771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29771 :=
  CNF.rup_sound cl_29771 [cl_23383,cl_23301,cl_23284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23383 v h) (hints_cons _ _ _ (der_23301 v h) (hints_cons _ _ _ (der_23284 v h) (by intro d hd; cases hd))))
def cl_29772 : CNF.NClause := [(16,false),(66,true),(11,false),(21,true)]
theorem der_29772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29772 :=
  CNF.rup_sound cl_29772 [cl_23301,cl_23337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23301 v h) (hints_cons _ _ _ (der_23337 v h) (by intro d hd; cases hd)))
def cl_29773 : CNF.NClause := [(77,true),(19,false),(15,false),(16,true)]
theorem der_29773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29773 :=
  CNF.rup_sound cl_29773 [cl_23448,cl_23447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23448 v h) (hints_cons _ _ _ (der_23447 v h) (by intro d hd; cases hd)))
def cl_29774 : CNF.NClause := [(66,true),(11,false),(1,false),(16,true)]
theorem der_29774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29774 :=
  CNF.rup_sound cl_29774 [cl_23285,cl_23281,cl_23500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23285 v h) (hints_cons _ _ _ (der_23281 v h) (hints_cons _ _ _ (der_23500 v h) (by intro d hd; cases hd))))
def cl_29775 : CNF.NClause := [(82,true),(8,false),(9,false),(6,true)]
theorem der_29775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29775 :=
  CNF.rup_sound cl_29775 [cl_23314,cl_23302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23314 v h) (hints_cons _ _ _ (der_23302 v h) (by intro d hd; cases hd)))
def cl_29776 : CNF.NClause := [(72,true),(11,false),(10,false),(12,true)]
theorem der_29776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29776 :=
  CNF.rup_sound cl_29776 [cl_23470,cl_23468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23470 v h) (hints_cons _ _ _ (der_23468 v h) (by intro d hd; cases hd)))
def cl_29777 : CNF.NClause := [(7,false),(17,false),(64,true),(22,true)]
theorem der_29777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29777 :=
  CNF.rup_sound cl_29777 [cl_23364,cl_23350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23364 v h) (hints_cons _ _ _ (der_23350 v h) (by intro d hd; cases hd)))
def cl_29778 : CNF.NClause := [(7,false),(12,false),(64,true),(22,true)]
theorem der_29778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29778 :=
  CNF.rup_sound cl_29778 [cl_29777,cl_23365,cl_23446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29777 v h) (hints_cons _ _ _ (der_23365 v h) (hints_cons _ _ _ (der_23446 v h) (by intro d hd; cases hd))))
def cl_29779 : CNF.NClause := [(22,false),(17,false),(64,true),(7,true)]
theorem der_29779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29779 :=
  CNF.rup_sound cl_29779 [cl_29766,cl_15054,cl_23317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29766 v h) (hints_cons _ _ _ (der_15054 v h) (hints_cons _ _ _ (der_23317 v h) (by intro d hd; cases hd))))
def cl_29780 : CNF.NClause := [(3,false),(65,true),(23,false),(8,true)]
theorem der_29780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29780 :=
  CNF.rup_sound cl_29780 [cl_23464,cl_23463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23464 v h) (hints_cons _ _ _ (der_23463 v h) (by intro d hd; cases hd)))
def cl_29781 : CNF.NClause := [(77,true),(19,false),(15,false),(18,true)]
theorem der_29781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29781 :=
  CNF.rup_sound cl_29781 [cl_29773,cl_23452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29773 v h) (hints_cons _ _ _ (der_23452 v h) (by intro d hd; cases hd)))
def cl_29782 : CNF.NClause := [(92,false),(20,true),(5,true),(15,true)]
theorem der_29782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29782 :=
  CNF.rup_sound cl_29782 [cl_15771,cl_15781,cl_15786,cl_15666,cl_15776,cl_15422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_15666 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (der_15422 v h) (by intro d hd; cases hd)))))))
def cl_29783 : CNF.NClause := [(92,false),(10,true),(5,true),(15,true)]
theorem der_29783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29783 :=
  CNF.rup_sound cl_29783 [cl_15871,cl_15881,cl_15876,cl_15716,cl_15886,cl_15416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_15716 v h) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_15416 v h) (by intro d hd; cases hd)))))))
def cl_29784 : CNF.NClause := [(92,false),(10,true),(20,true),(15,true)]
theorem der_29784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29784 :=
  CNF.rup_sound cl_29784 [cl_15886,cl_15881,cl_15876,cl_15716,cl_15871,cl_15423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_15716 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_15423 v h) (by intro d hd; cases hd)))))))
def cl_29785 : CNF.NClause := [(72,true),(13,false),(10,false),(11,true)]
theorem der_29785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29785 :=
  CNF.rup_sound cl_29785 [cl_23396,cl_23426,cl_23397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23396 v h) (hints_cons _ _ _ (der_23426 v h) (hints_cons _ _ _ (der_23397 v h) (by intro d hd; cases hd))))
def cl_29786 : CNF.NClause := [(16,false),(66,true),(1,false),(11,true)]
theorem der_29786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29786 :=
  CNF.rup_sound cl_29786 [cl_29771,cl_23381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29771 v h) (hints_cons _ _ _ (der_23381 v h) (by intro d hd; cases hd)))
def cl_29787 : CNF.NClause := [(62,false),(29,true),(26,true),(27,true)]
theorem der_29787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29787 :=
  CNF.rup_sound cl_29787 [cl_15892,cl_15891,cl_15894,cl_15667,cl_15893,cl_15012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15012 v h) (by intro d hd; cases hd)))))))
def cl_29788 : CNF.NClause := [(62,false),(28,true),(26,true),(27,true)]
theorem der_29788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29788 :=
  CNF.rup_sound cl_29788 [cl_15892,cl_15891,cl_15893,cl_15667,cl_15894,cl_15008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_15008 v h) (by intro d hd; cases hd)))))))
def cl_29789 : CNF.NClause := [(62,false),(28,true),(29,true),(27,true)]
theorem der_29789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29789 :=
  CNF.rup_sound cl_29789 [cl_15892,cl_15894,cl_15893,cl_15667,cl_15891,cl_15015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15015 v h) (by intro d hd; cases hd)))))))
def cl_29790 : CNF.NClause := [(63,true),(4,false),(24,false),(19,true)]
theorem der_29790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29790 :=
  CNF.rup_sound cl_29790 [cl_23476,cl_23472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23476 v h) (hints_cons _ _ _ (der_23472 v h) (by intro d hd; cases hd)))
def cl_29791 : CNF.NClause := [(62,false),(28,true),(29,true),(26,true)]
theorem der_29791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29791 :=
  CNF.rup_sound cl_29791 [cl_15894,cl_15891,cl_15893,cl_15667,cl_15892,cl_15014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_15014 v h) (by intro d hd; cases hd)))))))
def cl_29792 : CNF.NClause := [(87,false),(4,true),(3,true),(1,true)]
theorem der_29792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29792 :=
  CNF.rup_sound cl_29792 [cl_15769,cl_15767,cl_15770,cl_15661,cl_15768,cl_15280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_15280 v h) (by intro d hd; cases hd)))))))
def cl_29793 : CNF.NClause := [(16,false),(66,true),(11,false),(1,true)]
theorem der_29793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29793 :=
  CNF.rup_sound cl_29793 [cl_29772,cl_23333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29772 v h) (hints_cons _ _ _ (der_23333 v h) (by intro d hd; cases hd)))
def cl_29794 : CNF.NClause := [(92,false),(10,true),(20,true),(5,true)]
theorem der_29794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29794 :=
  CNF.rup_sound cl_29794 [cl_15871,cl_15886,cl_15876,cl_15716,cl_15881,cl_15420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_15716 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_15420 v h) (by intro d hd; cases hd)))))))
def cl_29795 : CNF.NClause := [(16,false),(77,true),(15,false),(17,true)]
theorem der_29795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29795 :=
  CNF.rup_sound cl_29795 [cl_23453,cl_29781,cl_23454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23453 v h) (hints_cons _ _ _ (der_29781 v h) (hints_cons _ _ _ (der_23454 v h) (by intro d hd; cases hd))))
def cl_29796 : CNF.NClause := [(67,true),(22,false),(24,false),(20,true)]
theorem der_29796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29796 :=
  CNF.rup_sound cl_29796 [cl_23326,cl_23327,cl_23323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23326 v h) (hints_cons _ _ _ (der_23327 v h) (hints_cons _ _ _ (der_23323 v h) (by intro d hd; cases hd))))
def cl_29797 : CNF.NClause := [(67,true),(22,false),(23,false),(24,true)]
theorem der_29797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29797 :=
  CNF.rup_sound cl_29797 [cl_23330,cl_23254,cl_23370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23330 v h) (hints_cons _ _ _ (der_23254 v h) (hints_cons _ _ _ (der_23370 v h) (by intro d hd; cases hd))))
def cl_29798 : CNF.NClause := [(63,true),(4,false),(19,false),(24,true)]
theorem der_29798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29798 :=
  CNF.rup_sound cl_29798 [cl_23477,cl_23473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23477 v h) (hints_cons _ _ _ (der_23473 v h) (by intro d hd; cases hd)))
def cl_29799 : CNF.NClause := [(82,true),(6,false),(8,false),(9,true)]
theorem der_29799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29799 :=
  CNF.rup_sound cl_29799 [cl_23312,cl_23311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23312 v h) (hints_cons _ _ _ (der_23311 v h) (by intro d hd; cases hd)))
def cl_29800 : CNF.NClause := [(8,false),(13,false),(65,true),(3,true)]
theorem der_29800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29800 :=
  CNF.rup_sound cl_29800 [cl_23413,cl_23411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23413 v h) (hints_cons _ _ _ (der_23411 v h) (by intro d hd; cases hd)))
def cl_29801 : CNF.NClause := [(67,true),(22,false),(20,false),(23,true)]
theorem der_29801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29801 :=
  CNF.rup_sound cl_29801 [cl_23256,cl_23342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23256 v h) (hints_cons _ _ _ (der_23342 v h) (by intro d hd; cases hd)))
def cl_29802 : CNF.NClause := [(8,false),(3,false),(65,true),(23,true)]
theorem der_29802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29802 :=
  CNF.rup_sound cl_29802 [cl_23460,cl_23240,cl_23459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23460 v h) (hints_cons _ _ _ (der_23240 v h) (hints_cons _ _ _ (der_23459 v h) (by intro d hd; cases hd))))
def cl_29803 : CNF.NClause := [(63,true),(19,false),(24,false),(4,true)]
theorem der_29803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29803 :=
  CNF.rup_sound cl_29803 [cl_23478,cl_23439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23478 v h) (hints_cons _ _ _ (der_23439 v h) (by intro d hd; cases hd)))
def cl_29804 : CNF.NClause := [(3,false),(65,true),(23,false),(13,true)]
theorem der_29804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29804 :=
  CNF.rup_sound cl_29804 [cl_29780,cl_23458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29780 v h) (hints_cons _ _ _ (der_23458 v h) (by intro d hd; cases hd)))
def cl_29805 : CNF.NClause := [(28,false),(4,false),(10,false),(73,true)]
theorem der_29805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29805 :=
  CNF.rup_sound cl_29805 [cl_23499,cl_24676,cl_24665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23499 v h) (hints_cons _ _ _ (der_24676 v h) (hints_cons _ _ _ (der_24665 v h) (by intro d hd; cases hd))))
def cl_29806 : CNF.NClause := [(63,true),(4,false),(19,false),(24,false)]
theorem der_29806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29806 :=
  CNF.rup_sound cl_29806 [cl_23475,cl_23471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23475 v h) (hints_cons _ _ _ (der_23471 v h) (by intro d hd; cases hd)))
def cl_29807 : CNF.NClause := [(72,true),(11,false),(10,false)]
theorem der_29807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29807 :=
  CNF.rup_sound cl_29807 [cl_29776,cl_23467,cl_23469,cl_23243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29776 v h) (hints_cons _ _ _ (der_23467 v h) (hints_cons _ _ _ (der_23469 v h) (hints_cons _ _ _ (der_23243 v h) (by intro d hd; cases hd)))))
def cl_29808 : CNF.NClause := [(16,false),(77,true),(17,false),(15,false)]
theorem der_29808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29808 :=
  CNF.rup_sound cl_29808 [cl_23232,cl_29781,cl_23229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23232 v h) (hints_cons _ _ _ (der_29781 v h) (hints_cons _ _ _ (der_23229 v h) (by intro d hd; cases hd))))
def cl_29809 : CNF.NClause := [(3,false),(65,true),(23,false)]
theorem der_29809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29809 :=
  CNF.rup_sound cl_29809 [cl_29804,cl_29780,cl_23239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29804 v h) (hints_cons _ _ _ (der_29780 v h) (hints_cons _ _ _ (der_23239 v h) (by intro d hd; cases hd))))
def cl_29810 : CNF.NClause := [(16,false),(77,true),(17,false),(19,false)]
theorem der_29810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29810 :=
  CNF.rup_sound cl_29810 [cl_29808,cl_23375,cl_23373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29808 v h) (hints_cons _ _ _ (der_23375 v h) (hints_cons _ _ _ (der_23373 v h) (by intro d hd; cases hd))))
def cl_29811 : CNF.NClause := [(22,false),(17,false),(64,true)]
theorem der_29811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29811 :=
  CNF.rup_sound cl_29811 [cl_29779,cl_29770,cl_23348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29779 v h) (hints_cons _ _ _ (der_29770 v h) (hints_cons _ _ _ (der_23348 v h) (by intro d hd; cases hd))))
def cl_29812 : CNF.NClause := [(82,true),(6,false),(9,false),(5,false)]
theorem der_29812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29812 :=
  CNF.rup_sound cl_29812 [cl_23315,cl_23275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23315 v h) (hints_cons _ _ _ (der_23275 v h) (by intro d hd; cases hd)))
def cl_29813 : CNF.NClause := [(66,true),(11,false),(1,false)]
theorem der_29813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29813 :=
  CNF.rup_sound cl_29813 [cl_29774,cl_29772,cl_15113,cl_23484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29774 v h) (hints_cons _ _ _ (der_29772 v h) (hints_cons _ _ _ (der_15113 v h) (hints_cons _ _ _ (der_23484 v h) (by intro d hd; cases hd)))))
def cl_29814 : CNF.NClause := [(12,false),(72,true),(13,false),(11,false)]
theorem der_29814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29814 :=
  CNF.rup_sound cl_29814 [cl_29807,cl_23425,cl_23419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29807 v h) (hints_cons _ _ _ (der_23425 v h) (hints_cons _ _ _ (der_23419 v h) (by intro d hd; cases hd))))
def cl_29815 : CNF.NClause := [(82,true),(6,false),(8,false),(9,false)]
theorem der_29815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29815 :=
  CNF.rup_sound cl_29815 [cl_23308,cl_23307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23308 v h) (hints_cons _ _ _ (der_23307 v h) (by intro d hd; cases hd)))
def cl_29816 : CNF.NClause := [(79,true),(15,false),(26,false),(2,true),(14,true)]
theorem der_29816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29816 :=
  CNF.rup_sound cl_29816 [cl_23643,cl_24294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23643 v h) (hints_cons _ _ _ (der_24294 v h) (by intro d hd; cases hd)))
def cl_29817 : CNF.NClause := [(8,false),(79,true),(15,false),(2,true),(14,true)]
theorem der_29817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29817 :=
  CNF.rup_sound cl_29817 [cl_23513,cl_23509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23513 v h) (hints_cons _ _ _ (der_23509 v h) (by intro d hd; cases hd)))
def cl_29818 : CNF.NClause := [(79,true),(15,false),(26,false),(21,true),(14,true)]
theorem der_29818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29818 :=
  CNF.rup_sound cl_29818 [cl_29816,cl_23965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29816 v h) (hints_cons _ _ _ (der_23965 v h) (by intro d hd; cases hd)))
def cl_29819 : CNF.NClause := [(8,false),(79,true),(15,false),(21,true),(14,true)]
theorem der_29819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29819 :=
  CNF.rup_sound cl_29819 [cl_23513,cl_23651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23513 v h) (hints_cons _ _ _ (der_23651 v h) (by intro d hd; cases hd)))
def cl_29820 : CNF.NClause := [(89,false),(27,true),(7,true),(16,true),(14,true)]
theorem der_29820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29820 :=
  CNF.rup_sound cl_29820 [cl_15780,cl_15773,cl_15782,cl_15792,cl_15663,cl_15789,cl_15336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_15336 v h) (by intro d hd; cases hd))))))))
def cl_29821 : CNF.NClause := [(89,false),(23,true),(7,true),(16,true),(14,true)]
theorem der_29821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29821 :=
  CNF.rup_sound cl_29821 [cl_15780,cl_15773,cl_15782,cl_15789,cl_15663,cl_15792,cl_15328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_15328 v h) (by intro d hd; cases hd))))))))
def cl_29822 : CNF.NClause := [(89,false),(23,true),(27,true),(16,true),(14,true)]
theorem der_29822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29822 :=
  CNF.rup_sound cl_29822 [cl_15780,cl_15792,cl_15782,cl_15789,cl_15663,cl_15773,cl_15343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15343 v h) (by intro d hd; cases hd))))))))
def cl_29823 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(14,true)]
theorem der_29823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29823 :=
  CNF.rup_sound cl_29823 [cl_15920,cl_15917,cl_15918,cl_15916,cl_15739,cl_15919,cl_15198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_15198 v h) (by intro d hd; cases hd))))))))
def cl_29824 : CNF.NClause := [(72,false),(13,true),(11,true),(12,true),(14,true)]
theorem der_29824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29824 :=
  CNF.rup_sound cl_29824 [cl_15920,cl_15917,cl_15918,cl_15919,cl_15739,cl_15916,cl_15205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_15205 v h) (by intro d hd; cases hd))))))))
def cl_29825 : CNF.NClause := [(29,false),(5,false),(86,true),(22,true),(14,true)]
theorem der_29825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29825 :=
  CNF.rup_sound cl_29825 [cl_24229,cl_24227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24229 v h) (hints_cons _ _ _ (der_24227 v h) (by intro d hd; cases hd)))
def cl_29826 : CNF.NClause := [(89,false),(23,true),(27,true),(7,true),(14,true)]
theorem der_29826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29826 :=
  CNF.rup_sound cl_29826 [cl_15780,cl_15773,cl_15792,cl_15789,cl_15663,cl_15782,cl_15340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15340 v h) (by intro d hd; cases hd))))))))
def cl_29827 : CNF.NClause := [(29,false),(5,false),(86,true),(18,true),(14,true)]
theorem der_29827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29827 :=
  CNF.rup_sound cl_29827 [cl_29825,cl_24225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29825 v h) (hints_cons _ _ _ (der_24225 v h) (by intro d hd; cases hd)))
def cl_29828 : CNF.NClause := [(21,false),(8,false),(79,true),(15,true),(14,true)]
theorem der_29828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29828 :=
  CNF.rup_sound cl_29828 [cl_23511,cl_23605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23511 v h) (hints_cons _ _ _ (der_23605 v h) (by intro d hd; cases hd)))
def cl_29829 : CNF.NClause := [(72,false),(13,true),(10,true),(11,true),(14,true)]
theorem der_29829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29829 :=
  CNF.rup_sound cl_29829 [cl_15920,cl_15917,cl_15916,cl_15919,cl_15739,cl_15918,cl_15202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_15202 v h) (by intro d hd; cases hd))))))))
def cl_29830 : CNF.NClause := [(63,false),(4,true),(9,true),(19,true),(14,true)]
theorem der_29830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29830 :=
  CNF.rup_sound cl_29830 [cl_15875,cl_15885,cl_15880,cl_15870,cl_15668,cl_15890,cl_15032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_15870 v h) (hints_cons _ _ _ (der_15668 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_15032 v h) (by intro d hd; cases hd))))))))
def cl_29831 : CNF.NClause := [(22,false),(29,false),(86,true),(5,true),(14,true)]
theorem der_29831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29831 :=
  CNF.rup_sound cl_29831 [cl_24140,cl_24139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24140 v h) (hints_cons _ _ _ (der_24139 v h) (by intro d hd; cases hd)))
def cl_29832 : CNF.NClause := [(3,false),(20,false),(70,true),(17,true),(14,true)]
theorem der_29832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29832 :=
  CNF.rup_sound cl_29832 [cl_24028,cl_24024,cl_24585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24028 v h) (hints_cons _ _ _ (der_24024 v h) (hints_cons _ _ _ (der_24585 v h) (by intro d hd; cases hd))))
def cl_29833 : CNF.NClause := [(29,false),(27,false),(62,true)]
theorem der_29833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29833 :=
  CNF.rup_sound cl_29833 [cl_23166,cl_29765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23166 v h) (hints_cons _ _ _ (der_29765 v h) (by intro d hd; cases hd)))
def cl_29834 : CNF.NClause := [(62,true),(27,false),(28,false)]
theorem der_29834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29834 :=
  CNF.rup_sound cl_29834 [cl_23167,cl_29765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23167 v h) (hints_cons _ _ _ (der_29765 v h) (by intro d hd; cases hd)))
def cl_29835 : CNF.NClause := [(62,true),(29,false),(26,false)]
theorem der_29835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29835 :=
  CNF.rup_sound cl_29835 [cl_23174,cl_29765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23174 v h) (hints_cons _ _ _ (der_29765 v h) (by intro d hd; cases hd)))
def cl_29836 : CNF.NClause := [(62,true),(28,false),(26,false)]
theorem der_29836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29836 :=
  CNF.rup_sound cl_29836 [cl_23175,cl_29765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23175 v h) (hints_cons _ _ _ (der_29765 v h) (by intro d hd; cases hd)))
def cl_29837 : CNF.NClause := [(27,false),(26,false),(62,true)]
theorem der_29837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29837 :=
  CNF.rup_sound cl_29837 [cl_23183,cl_29836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23183 v h) (hints_cons _ _ _ (der_29836 v h) (by intro d hd; cases hd)))
def cl_29838 : CNF.NClause := [(92,true),(20,false),(5,false)]
theorem der_29838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29838 :=
  CNF.rup_sound cl_29838 [cl_23185,cl_23184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23185 v h) (hints_cons _ _ _ (der_23184 v h) (by intro d hd; cases hd)))
def cl_29839 : CNF.NClause := [(92,true),(5,false),(15,false)]
theorem der_29839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29839 :=
  CNF.rup_sound cl_29839 [cl_23186,cl_23184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23186 v h) (hints_cons _ _ _ (der_23184 v h) (by intro d hd; cases hd)))
def cl_29840 : CNF.NClause := [(92,true),(15,false),(20,false)]
theorem der_29840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29840 :=
  CNF.rup_sound cl_29840 [cl_23187,cl_23184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23187 v h) (hints_cons _ _ _ (der_23184 v h) (by intro d hd; cases hd)))
def cl_29841 : CNF.NClause := [(87,true),(3,false),(1,false)]
theorem der_29841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29841 :=
  CNF.rup_sound cl_29841 [cl_23188,cl_23158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23188 v h) (hints_cons _ _ _ (der_23158 v h) (by intro d hd; cases hd)))
def cl_29842 : CNF.NClause := [(64,true),(7,false),(17,false)]
theorem der_29842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29842 :=
  CNF.rup_sound cl_29842 [cl_29777,cl_29811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29777 v h) (hints_cons _ _ _ (der_29811 v h) (by intro d hd; cases hd)))
def cl_29843 : CNF.NClause := [(64,true),(12,false),(7,false)]
theorem der_29843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29843 :=
  CNF.rup_sound cl_29843 [cl_29778,cl_29766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29778 v h) (hints_cons _ _ _ (der_29766 v h) (by intro d hd; cases hd)))
def cl_29844 : CNF.NClause := [(64,true),(22,false),(17,false)]
theorem der_29844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29844 :=
  CNF.rup_sound cl_29844 [cl_29779,cl_29842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29779 v h) (hints_cons _ _ _ (der_29842 v h) (by intro d hd; cases hd)))
def cl_29845 : CNF.NClause := [(72,true),(10,false),(13,false)]
theorem der_29845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29845 :=
  CNF.rup_sound cl_29845 [cl_29785,cl_29807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29785 v h) (hints_cons _ _ _ (der_29807 v h) (by intro d hd; cases hd)))
def cl_29846 : CNF.NClause := [(66,true),(16,false),(1,false)]
theorem der_29846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29846 :=
  CNF.rup_sound cl_29846 [cl_29786,cl_29813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29786 v h) (hints_cons _ _ _ (der_29813 v h) (by intro d hd; cases hd)))
def cl_29847 : CNF.NClause := [(66,true),(16,false),(11,false)]
theorem der_29847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29847 :=
  CNF.rup_sound cl_29847 [cl_29793,cl_29813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29793 v h) (hints_cons _ _ _ (der_29813 v h) (by intro d hd; cases hd)))
def cl_29848 : CNF.NClause := [(3,false),(65,true),(8,false)]
theorem der_29848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29848 :=
  CNF.rup_sound cl_29848 [cl_29802,cl_29809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29802 v h) (hints_cons _ _ _ (der_29809 v h) (by intro d hd; cases hd)))
def cl_29849 : CNF.NClause := [(63,true),(24,false),(4,false)]
theorem der_29849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29849 :=
  CNF.rup_sound cl_29849 [cl_29806,cl_29790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29806 v h) (hints_cons _ _ _ (der_29790 v h) (by intro d hd; cases hd)))
def cl_29850 : CNF.NClause := [(77,true),(16,false),(15,false)]
theorem der_29850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29850 :=
  CNF.rup_sound cl_29850 [cl_29808,cl_29795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29808 v h) (hints_cons _ _ _ (der_29795 v h) (by intro d hd; cases hd)))
def cl_29851 : CNF.NClause := [(82,true),(6,false),(8,false)]
theorem der_29851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29851 :=
  CNF.rup_sound cl_29851 [cl_29815,cl_29799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29815 v h) (hints_cons _ _ _ (der_29799 v h) (by intro d hd; cases hd)))
def cl_29852 : CNF.NClause := [(3,false),(18,false),(23,true),(65,true)]
theorem der_29852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29852 :=
  CNF.rup_sound cl_29852 [cl_23198,cl_29848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23198 v h) (hints_cons _ _ _ (der_29848 v h) (by intro d hd; cases hd)))
def cl_29853 : CNF.NClause := [(29,false),(28,false),(26,true),(62,true)]
theorem der_29853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29853 :=
  CNF.rup_sound cl_29853 [cl_15004,cl_29834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15004 v h) (hints_cons _ _ _ (der_29834 v h) (by intro d hd; cases hd)))
def cl_29854 : CNF.NClause := [(91,true),(6,false),(18,true),(12,false)]
theorem der_29854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29854 :=
  CNF.rup_sound cl_29854 [cl_23203,cl_23201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23203 v h) (hints_cons _ _ _ (der_23201 v h) (by intro d hd; cases hd)))
def cl_29855 : CNF.NClause := [(91,true),(18,true),(6,false),(26,false)]
theorem der_29855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29855 :=
  CNF.rup_sound cl_29855 [cl_23205,cl_23201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23205 v h) (hints_cons _ _ _ (der_23201 v h) (by intro d hd; cases hd)))
def cl_29856 : CNF.NClause := [(89,true),(27,true),(16,false),(23,false)]
theorem der_29856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29856 :=
  CNF.rup_sound cl_29856 [cl_23219,cl_23216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23219 v h) (hints_cons _ _ _ (der_23216 v h) (by intro d hd; cases hd)))
def cl_29857 : CNF.NClause := [(89,true),(27,false),(14,true),(23,false)]
theorem der_29857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29857 :=
  CNF.rup_sound cl_29857 [cl_23221,cl_23220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23221 v h) (hints_cons _ _ _ (der_23220 v h) (by intro d hd; cases hd)))
def cl_29858 : CNF.NClause := [(64,true),(17,false),(7,true),(12,false)]
theorem der_29858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29858 :=
  CNF.rup_sound cl_29858 [cl_23226,cl_29844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23226 v h) (hints_cons _ _ _ (der_29844 v h) (by intro d hd; cases hd)))
def cl_29859 : CNF.NClause := [(77,true),(18,true),(15,false),(17,false)]
theorem der_29859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29859 :=
  CNF.rup_sound cl_29859 [cl_23229,cl_29781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23229 v h) (hints_cons _ _ _ (der_29781 v h) (by intro d hd; cases hd)))
def cl_29860 : CNF.NClause := [(23,false),(65,true),(3,true),(13,false)]
theorem der_29860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29860 :=
  CNF.rup_sound cl_29860 [cl_23235,cl_29800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23235 v h) (hints_cons _ _ _ (der_29800 v h) (by intro d hd; cases hd)))
def cl_29861 : CNF.NClause := [(23,true),(3,false),(13,false),(65,true)]
theorem der_29861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29861 :=
  CNF.rup_sound cl_29861 [cl_23240,cl_29852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23240 v h) (hints_cons _ _ _ (der_29852 v h) (by intro d hd; cases hd)))
def cl_29862 : CNF.NClause := [(14,true),(9,false),(4,false),(63,true)]
theorem der_29862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29862 :=
  CNF.rup_sound cl_29862 [cl_23250,cl_29849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23250 v h) (hints_cons _ _ _ (der_29849 v h) (by intro d hd; cases hd)))
def cl_29863 : CNF.NClause := [(67,true),(21,true),(20,false),(22,false)]
theorem der_29863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29863 :=
  CNF.rup_sound cl_29863 [cl_23254,cl_29801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23254 v h) (hints_cons _ _ _ (der_29801 v h) (by intro d hd; cases hd)))
def cl_29864 : CNF.NClause := [(1,false),(66,true),(6,true),(21,false)]
theorem der_29864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29864 :=
  CNF.rup_sound cl_29864 [cl_23282,cl_29813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23282 v h) (hints_cons _ _ _ (der_29813 v h) (by intro d hd; cases hd)))
def cl_29865 : CNF.NClause := [(82,true),(5,false),(9,false),(7,true)]
theorem der_29865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29865 :=
  CNF.rup_sound cl_29865 [cl_23289,cl_29812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23289 v h) (hints_cons _ _ _ (der_29812 v h) (by intro d hd; cases hd)))
def cl_29866 : CNF.NClause := [(82,true),(7,true),(8,false),(5,false)]
theorem der_29866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29866 :=
  CNF.rup_sound cl_29866 [cl_23291,cl_29865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23291 v h) (hints_cons _ _ _ (der_29865 v h) (by intro d hd; cases hd)))
def cl_29867 : CNF.NClause := [(91,true),(26,false),(18,true),(24,false)]
theorem der_29867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29867 :=
  CNF.rup_sound cl_29867 [cl_23293,cl_29855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23293 v h) (hints_cons _ _ _ (der_29855 v h) (by intro d hd; cases hd)))
def cl_29868 : CNF.NClause := [(91,true),(12,false),(18,true),(24,false)]
theorem der_29868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29868 :=
  CNF.rup_sound cl_29868 [cl_23297,cl_29867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23297 v h) (hints_cons _ _ _ (der_29867 v h) (by intro d hd; cases hd)))
def cl_29869 : CNF.NClause := [(6,true),(9,false),(7,false),(82,true)]
theorem der_29869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29869 :=
  CNF.rup_sound cl_29869 [cl_23303,cl_29775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23303 v h) (hints_cons _ _ _ (der_29775 v h) (by intro d hd; cases hd)))
def cl_29870 : CNF.NClause := [(82,true),(8,false),(7,false),(9,true)]
theorem der_29870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29870 :=
  CNF.rup_sound cl_29870 [cl_23304,cl_29851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23304 v h) (hints_cons _ _ _ (der_29851 v h) (by intro d hd; cases hd)))
def cl_29871 : CNF.NClause := [(91,true),(6,true),(18,false),(24,false)]
theorem der_29871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29871 :=
  CNF.rup_sound cl_29871 [cl_23306,cl_23296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23306 v h) (hints_cons _ _ _ (der_23296 v h) (by intro d hd; cases hd)))
def cl_29872 : CNF.NClause := [(82,true),(9,false),(5,true),(6,false)]
theorem der_29872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29872 :=
  CNF.rup_sound cl_29872 [cl_23310,cl_29851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23310 v h) (hints_cons _ _ _ (der_29851 v h) (by intro d hd; cases hd)))
def cl_29873 : CNF.NClause := [(82,true),(9,true),(6,false),(7,false)]
theorem der_29873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29873 :=
  CNF.rup_sound cl_29873 [cl_23313,cl_29851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23313 v h) (hints_cons _ _ _ (der_29851 v h) (by intro d hd; cases hd)))
def cl_29874 : CNF.NClause := [(82,true),(9,false),(7,true),(8,false)]
theorem der_29874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29874 :=
  CNF.rup_sound cl_29874 [cl_23314,cl_29851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23314 v h) (hints_cons _ _ _ (der_29851 v h) (by intro d hd; cases hd)))
def cl_29875 : CNF.NClause := [(82,true),(7,true),(6,false),(5,false)]
theorem der_29875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29875 :=
  CNF.rup_sound cl_29875 [cl_23316,cl_29812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23316 v h) (hints_cons _ _ _ (der_29812 v h) (by intro d hd; cases hd)))
def cl_29876 : CNF.NClause := [(22,true),(64,true),(17,false),(2,false)]
theorem der_29876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29876 :=
  CNF.rup_sound cl_29876 [cl_23319,cl_29842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23319 v h) (hints_cons _ _ _ (der_29842 v h) (by intro d hd; cases hd)))
def cl_29877 : CNF.NClause := [(67,true),(21,true),(23,false),(22,false)]
theorem der_29877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29877 :=
  CNF.rup_sound cl_29877 [cl_23323,cl_29797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23323 v h) (hints_cons _ _ _ (der_29797 v h) (by intro d hd; cases hd)))
def cl_29878 : CNF.NClause := [(67,true),(21,true),(24,false),(23,false)]
theorem der_29878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29878 :=
  CNF.rup_sound cl_29878 [cl_23325,cl_29877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23325 v h) (hints_cons _ _ _ (der_29877 v h) (by intro d hd; cases hd)))
def cl_29879 : CNF.NClause := [(67,true),(21,true),(22,false),(24,false)]
theorem der_29879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29879 :=
  CNF.rup_sound cl_29879 [cl_23327,cl_29878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23327 v h) (hints_cons _ _ _ (der_29878 v h) (by intro d hd; cases hd)))
def cl_29880 : CNF.NClause := [(67,true),(20,true),(23,false),(22,false)]
theorem der_29880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29880 :=
  CNF.rup_sound cl_29880 [cl_23330,cl_29796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23330 v h) (hints_cons _ _ _ (der_29796 v h) (by intro d hd; cases hd)))
def cl_29881 : CNF.NClause := [(67,true),(20,true),(23,false),(21,false)]
theorem der_29881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29881 :=
  CNF.rup_sound cl_29881 [cl_23331,cl_29880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23331 v h) (hints_cons _ _ _ (der_29880 v h) (by intro d hd; cases hd)))
def cl_29882 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false)]
theorem der_29882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29882 :=
  CNF.rup_sound cl_29882 [cl_23332,cl_29796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23332 v h) (hints_cons _ _ _ (der_29796 v h) (by intro d hd; cases hd)))
def cl_29883 : CNF.NClause := [(66,true),(16,true),(11,false),(21,false)]
theorem der_29883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29883 :=
  CNF.rup_sound cl_29883 [cl_23335,cl_29813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23335 v h) (hints_cons _ _ _ (der_29813 v h) (by intro d hd; cases hd)))
def cl_29884 : CNF.NClause := [(16,false),(1,true),(6,false),(66,true)]
theorem der_29884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29884 :=
  CNF.rup_sound cl_29884 [cl_23338,cl_29847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23338 v h) (hints_cons _ _ _ (der_29847 v h) (by intro d hd; cases hd)))
def cl_29885 : CNF.NClause := [(21,true),(66,true),(6,false),(11,false)]
theorem der_29885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29885 :=
  CNF.rup_sound cl_29885 [cl_23339,cl_29772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23339 v h) (hints_cons _ _ _ (der_29772 v h) (by intro d hd; cases hd)))
def cl_29886 : CNF.NClause := [(89,true),(16,false),(27,true),(14,false)]
theorem der_29886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29886 :=
  CNF.rup_sound cl_29886 [cl_23345,cl_23343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23345 v h) (hints_cons _ _ _ (der_23343 v h) (by intro d hd; cases hd)))
def cl_29887 : CNF.NClause := [(64,true),(22,false),(12,true),(2,false)]
theorem der_29887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29887 :=
  CNF.rup_sound cl_29887 [cl_23349,cl_29811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23349 v h) (hints_cons _ _ _ (der_29811 v h) (by intro d hd; cases hd)))
def cl_29888 : CNF.NClause := [(17,true),(64,true),(2,false),(7,false)]
theorem der_29888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29888 :=
  CNF.rup_sound cl_29888 [cl_23351,cl_29843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23351 v h) (hints_cons _ _ _ (der_29843 v h) (by intro d hd; cases hd)))
def cl_29889 : CNF.NClause := [(91,true),(18,true),(24,false),(6,false)]
theorem der_29889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29889 :=
  CNF.rup_sound cl_29889 [cl_23356,cl_29867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23356 v h) (hints_cons _ _ _ (der_29867 v h) (by intro d hd; cases hd)))
def cl_29890 : CNF.NClause := [(22,false),(7,false),(2,true),(64,true)]
theorem der_29890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29890 :=
  CNF.rup_sound cl_29890 [cl_23362,cl_29844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23362 v h) (hints_cons _ _ _ (der_29844 v h) (by intro d hd; cases hd)))
def cl_29891 : CNF.NClause := [(7,false),(17,false),(2,true),(64,true)]
theorem der_29891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29891 :=
  CNF.rup_sound cl_29891 [cl_23364,cl_29844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23364 v h) (hints_cons _ _ _ (der_29844 v h) (by intro d hd; cases hd)))
def cl_29892 : CNF.NClause := [(7,false),(2,true),(12,false),(64,true)]
theorem der_29892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29892 :=
  CNF.rup_sound cl_29892 [cl_23365,cl_29842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23365 v h) (hints_cons _ _ _ (der_29842 v h) (by intro d hd; cases hd)))
def cl_29893 : CNF.NClause := [(91,true),(24,true),(6,false),(26,false)]
theorem der_29893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29893 :=
  CNF.rup_sound cl_29893 [cl_23371,cl_29855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23371 v h) (hints_cons _ _ _ (der_29855 v h) (by intro d hd; cases hd)))
def cl_29894 : CNF.NClause := [(77,true),(17,false),(19,false),(16,true)]
theorem der_29894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29894 :=
  CNF.rup_sound cl_29894 [cl_23372,cl_29773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23372 v h) (hints_cons _ _ _ (der_29773 v h) (by intro d hd; cases hd)))
def cl_29895 : CNF.NClause := [(18,true),(77,true),(19,false),(17,false)]
theorem der_29895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29895 :=
  CNF.rup_sound cl_29895 [cl_23375,cl_29859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23375 v h) (hints_cons _ _ _ (der_29859 v h) (by intro d hd; cases hd)))
def cl_29896 : CNF.NClause := [(17,true),(19,false),(77,true),(16,false)]
theorem der_29896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29896 :=
  CNF.rup_sound cl_29896 [cl_23376,cl_29795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23376 v h) (hints_cons _ _ _ (der_29795 v h) (by intro d hd; cases hd)))
def cl_29897 : CNF.NClause := [(17,true),(16,false),(18,false),(77,true)]
theorem der_29897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29897 :=
  CNF.rup_sound cl_29897 [cl_23378,cl_29795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23378 v h) (hints_cons _ _ _ (der_29795 v h) (by intro d hd; cases hd)))
def cl_29898 : CNF.NClause := [(15,true),(16,false),(17,false),(77,true)]
theorem der_29898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29898 :=
  CNF.rup_sound cl_29898 [cl_23379,cl_29810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23379 v h) (hints_cons _ _ _ (der_29810 v h) (by intro d hd; cases hd)))
def cl_29899 : CNF.NClause := [(16,true),(6,false),(21,false),(66,true)]
theorem der_29899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29899 :=
  CNF.rup_sound cl_29899 [cl_23382,cl_29883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23382 v h) (hints_cons _ _ _ (der_29883 v h) (by intro d hd; cases hd)))
def cl_29900 : CNF.NClause := [(21,true),(6,false),(1,false),(66,true)]
theorem der_29900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29900 :=
  CNF.rup_sound cl_29900 [cl_23384,cl_29771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23384 v h) (hints_cons _ _ _ (der_29771 v h) (by intro d hd; cases hd)))
def cl_29901 : CNF.NClause := [(90,true),(8,false),(11,true),(22,false)]
theorem der_29901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29901 :=
  CNF.rup_sound cl_29901 [cl_23390,cl_23389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23390 v h) (hints_cons _ _ _ (der_23389 v h) (by intro d hd; cases hd)))
def cl_29902 : CNF.NClause := [(72,true),(13,true),(14,false),(10,false)]
theorem der_29902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29902 :=
  CNF.rup_sound cl_29902 [cl_23395,cl_29807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23395 v h) (hints_cons _ _ _ (der_29807 v h) (by intro d hd; cases hd)))
def cl_29903 : CNF.NClause := [(90,true),(8,true),(19,false),(22,false)]
theorem der_29903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29903 :=
  CNF.rup_sound cl_29903 [cl_23401,cl_23399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23401 v h) (hints_cons _ _ _ (der_23399 v h) (by intro d hd; cases hd)))
def cl_29904 : CNF.NClause := [(66,true),(16,false),(6,true),(21,false)]
theorem der_29904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29904 :=
  CNF.rup_sound cl_29904 [cl_23402,cl_29847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23402 v h) (hints_cons _ _ _ (der_29847 v h) (by intro d hd; cases hd)))
def cl_29905 : CNF.NClause := [(72,true),(12,false),(13,false),(10,true)]
theorem der_29905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29905 :=
  CNF.rup_sound cl_29905 [cl_23405,cl_29814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23405 v h) (hints_cons _ _ _ (der_29814 v h) (by intro d hd; cases hd)))
def cl_29906 : CNF.NClause := [(90,true),(8,true),(22,false),(28,false)]
theorem der_29906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29906 :=
  CNF.rup_sound cl_29906 [cl_23406,cl_23399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23406 v h) (hints_cons _ _ _ (der_23399 v h) (by intro d hd; cases hd)))
def cl_29907 : CNF.NClause := [(18,true),(65,true),(8,false),(23,false)]
theorem der_29907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29907 :=
  CNF.rup_sound cl_29907 [cl_23410,cl_29809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23410 v h) (hints_cons _ _ _ (der_29809 v h) (by intro d hd; cases hd)))
def cl_29908 : CNF.NClause := [(65,true),(8,false),(3,true),(18,false)]
theorem der_29908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29908 :=
  CNF.rup_sound cl_29908 [cl_23412,cl_29800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23412 v h) (hints_cons _ _ _ (der_29800 v h) (by intro d hd; cases hd)))
def cl_29909 : CNF.NClause := [(18,true),(13,false),(65,true),(8,false)]
theorem der_29909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29909 :=
  CNF.rup_sound cl_29909 [cl_23413,cl_29848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23413 v h) (hints_cons _ _ _ (der_29848 v h) (by intro d hd; cases hd)))
def cl_29910 : CNF.NClause := [(90,true),(28,true),(8,false),(22,false)]
theorem der_29910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29910 :=
  CNF.rup_sound cl_29910 [cl_23414,cl_29901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23414 v h) (hints_cons _ _ _ (der_29901 v h) (by intro d hd; cases hd)))
def cl_29911 : CNF.NClause := [(90,true),(28,true),(11,false),(22,false)]
theorem der_29911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29911 :=
  CNF.rup_sound cl_29911 [cl_23415,cl_29910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23415 v h) (hints_cons _ _ _ (der_29910 v h) (by intro d hd; cases hd)))
def cl_29912 : CNF.NClause := [(91,true),(6,true),(18,false),(26,false)]
theorem der_29912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29912 :=
  CNF.rup_sound cl_29912 [cl_23416,cl_29871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23416 v h) (hints_cons _ _ _ (der_29871 v h) (by intro d hd; cases hd)))
def cl_29913 : CNF.NClause := [(91,true),(6,false),(12,false),(24,false)]
theorem der_29913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29913 :=
  CNF.rup_sound cl_29913 [cl_23418,cl_23417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23418 v h) (hints_cons _ _ _ (der_23417 v h) (by intro d hd; cases hd)))
def cl_29914 : CNF.NClause := [(13,true),(72,true),(12,false),(14,false)]
theorem der_29914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29914 :=
  CNF.rup_sound cl_29914 [cl_23421,cl_29902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23421 v h) (hints_cons _ _ _ (der_29902 v h) (by intro d hd; cases hd)))
def cl_29915 : CNF.NClause := [(12,true),(72,true),(14,false),(11,false)]
theorem der_29915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29915 :=
  CNF.rup_sound cl_29915 [cl_23422,cl_29807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23422 v h) (hints_cons _ _ _ (der_29807 v h) (by intro d hd; cases hd)))
def cl_29916 : CNF.NClause := [(72,true),(12,true),(13,false),(11,false)]
theorem der_29916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29916 :=
  CNF.rup_sound cl_29916 [cl_23424,cl_29915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23424 v h) (hints_cons _ _ _ (der_29915 v h) (by intro d hd; cases hd)))
def cl_29917 : CNF.NClause := [(12,false),(72,true),(11,false),(14,true)]
theorem der_29917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29917 :=
  CNF.rup_sound cl_29917 [cl_23425,cl_29807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23425 v h) (hints_cons _ _ _ (der_29807 v h) (by intro d hd; cases hd)))
def cl_29918 : CNF.NClause := [(12,true),(14,false),(13,false),(72,true)]
theorem der_29918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29918 :=
  CNF.rup_sound cl_29918 [cl_23426,cl_29915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23426 v h) (hints_cons _ _ _ (der_29915 v h) (by intro d hd; cases hd)))
def cl_29919 : CNF.NClause := [(14,true),(9,false),(63,true),(24,false)]
theorem der_29919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29919 :=
  CNF.rup_sound cl_29919 [cl_23430,cl_29862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23430 v h) (hints_cons _ _ _ (der_29862 v h) (by intro d hd; cases hd)))
def cl_29920 : CNF.NClause := [(63,true),(14,true),(9,false),(19,false)]
theorem der_29920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29920 :=
  CNF.rup_sound cl_29920 [cl_23432,cl_29919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23432 v h) (hints_cons _ _ _ (der_29919 v h) (by intro d hd; cases hd)))
def cl_29921 : CNF.NClause := [(90,true),(19,true),(22,false),(11,false)]
theorem der_29921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29921 :=
  CNF.rup_sound cl_29921 [cl_23435,cl_29911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23435 v h) (hints_cons _ _ _ (der_29911 v h) (by intro d hd; cases hd)))
def cl_29922 : CNF.NClause := [(90,true),(11,false),(19,true),(28,false)]
theorem der_29922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29922 :=
  CNF.rup_sound cl_29922 [cl_23436,cl_29921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23436 v h) (hints_cons _ _ _ (der_29921 v h) (by intro d hd; cases hd)))
def cl_29923 : CNF.NClause := [(90,true),(11,false),(8,false),(28,true)]
theorem der_29923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29923 :=
  CNF.rup_sound cl_29923 [cl_23437,cl_29911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23437 v h) (hints_cons _ _ _ (der_29911 v h) (by intro d hd; cases hd)))
def cl_29924 : CNF.NClause := [(63,true),(19,true),(14,false),(24,false)]
theorem der_29924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29924 :=
  CNF.rup_sound cl_29924 [cl_23440,cl_29790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23440 v h) (hints_cons _ _ _ (der_29790 v h) (by intro d hd; cases hd)))
def cl_29925 : CNF.NClause := [(63,true),(4,true),(19,false),(14,false)]
theorem der_29925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29925 :=
  CNF.rup_sound cl_29925 [cl_23441,cl_29803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23441 v h) (hints_cons _ _ _ (der_29803 v h) (by intro d hd; cases hd)))
def cl_29926 : CNF.NClause := [(89,true),(14,false),(23,false),(27,false)]
theorem der_29926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29926 :=
  CNF.rup_sound cl_29926 [cl_14722,cl_23189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14722 v h) (hints_cons _ _ _ (der_23189 v h) (by intro d hd; cases hd)))
def cl_29927 : CNF.NClause := [(89,true),(27,false),(23,true),(16,false)]
theorem der_29927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29927 :=
  CNF.rup_sound cl_29927 [cl_23443,cl_23344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23443 v h) (hints_cons _ _ _ (der_23344 v h) (by intro d hd; cases hd)))
def cl_29928 : CNF.NClause := [(89,true),(7,false),(23,false),(14,false)]
theorem der_29928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29928 :=
  CNF.rup_sound cl_29928 [cl_23445,cl_29926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23445 v h) (hints_cons _ _ _ (der_29926 v h) (by intro d hd; cases hd)))
def cl_29929 : CNF.NClause := [(77,true),(16,true),(18,false),(15,false)]
theorem der_29929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29929 :=
  CNF.rup_sound cl_29929 [cl_23449,cl_29773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23449 v h) (hints_cons _ _ _ (der_29773 v h) (by intro d hd; cases hd)))
def cl_29930 : CNF.NClause := [(18,true),(16,false),(15,false),(77,true)]
theorem der_29930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29930 :=
  CNF.rup_sound cl_29930 [cl_23454,cl_29781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23454 v h) (hints_cons _ _ _ (der_29781 v h) (by intro d hd; cases hd)))
def cl_29931 : CNF.NClause := [(12,false),(22,true),(2,false),(64,true)]
theorem der_29931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29931 :=
  CNF.rup_sound cl_29931 [cl_23455,cl_29843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23455 v h) (hints_cons _ _ _ (der_29843 v h) (by intro d hd; cases hd)))
def cl_29933 : CNF.NClause := [(3,true),(65,true),(18,false),(23,false)]
theorem der_29933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29933 :=
  CNF.rup_sound cl_29933 [cl_23461,cl_29908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23461 v h) (hints_cons _ _ _ (der_29908 v h) (by intro d hd; cases hd)))
def cl_29934 : CNF.NClause := [(18,true),(23,false),(3,false),(65,true)]
theorem der_29934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29934 :=
  CNF.rup_sound cl_29934 [cl_23464,cl_29848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23464 v h) (hints_cons _ _ _ (der_29848 v h) (by intro d hd; cases hd)))
def cl_29935 : CNF.NClause := [(13,true),(12,false),(72,true),(10,false)]
theorem der_29935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29935 :=
  CNF.rup_sound cl_29935 [cl_23469,cl_29902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23469 v h) (hints_cons _ _ _ (der_29902 v h) (by intro d hd; cases hd)))
def cl_29936 : CNF.NClause := [(63,true),(19,true),(14,false),(4,false)]
theorem der_29936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29936 :=
  CNF.rup_sound cl_29936 [cl_23474,cl_29790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23474 v h) (hints_cons _ _ _ (der_29790 v h) (by intro d hd; cases hd)))
def cl_29937 : CNF.NClause := [(63,true),(24,false),(4,false),(14,true)]
theorem der_29937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29937 :=
  CNF.rup_sound cl_29937 [cl_23475,cl_29790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23475 v h) (hints_cons _ _ _ (der_29790 v h) (by intro d hd; cases hd)))
def cl_29938 : CNF.NClause := [(67,true),(23,false),(20,false),(24,true)]
theorem der_29938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29938 :=
  CNF.rup_sound cl_29938 [cl_23480,cl_29797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23480 v h) (hints_cons _ _ _ (der_29797 v h) (by intro d hd; cases hd)))
def cl_29939 : CNF.NClause := [(21,false),(20,false),(67,true),(23,true)]
theorem der_29939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29939 :=
  CNF.rup_sound cl_29939 [cl_23481,cl_29801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23481 v h) (hints_cons _ _ _ (der_29801 v h) (by intro d hd; cases hd)))
def cl_29940 : CNF.NClause := [(67,true),(22,false),(24,false),(23,false)]
theorem der_29940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29940 :=
  CNF.rup_sound cl_29940 [cl_23482,cl_29796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23482 v h) (hints_cons _ _ _ (der_29796 v h) (by intro d hd; cases hd)))
def cl_29941 : CNF.NClause := [(67,true),(20,false),(24,false),(23,false)]
theorem der_29941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29941 :=
  CNF.rup_sound cl_29941 [cl_23483,cl_29940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23483 v h) (hints_cons _ _ _ (der_29940 v h) (by intro d hd; cases hd)))
def cl_29942 : CNF.NClause := [(88,true),(29,true),(17,false),(9,false)]
theorem der_29942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29942 :=
  CNF.rup_sound cl_29942 [cl_23492,cl_23366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23492 v h) (hints_cons _ _ _ (der_23366 v h) (by intro d hd; cases hd)))
def cl_29943 : CNF.NClause := [(88,true),(29,false),(17,false),(21,false)]
theorem der_29943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29943 :=
  CNF.rup_sound cl_29943 [cl_23494,cl_23486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23494 v h) (hints_cons _ _ _ (der_23486 v h) (by intro d hd; cases hd)))
def cl_29944 : CNF.NClause := [(88,true),(21,false),(9,true),(29,false)]
theorem der_29944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29944 :=
  CNF.rup_sound cl_29944 [cl_23495,cl_29943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23495 v h) (hints_cons _ _ _ (der_29943 v h) (by intro d hd; cases hd)))
def cl_29945 : CNF.NClause := [(88,true),(29,false),(17,true),(9,false)]
theorem der_29945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29945 :=
  CNF.rup_sound cl_29945 [cl_23496,cl_23490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23496 v h) (hints_cons _ _ _ (der_23490 v h) (by intro d hd; cases hd)))
def cl_29946 : CNF.NClause := [(88,true),(21,false),(29,true),(9,false)]
theorem der_29946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29946 :=
  CNF.rup_sound cl_29946 [cl_23497,cl_29942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23497 v h) (hints_cons _ _ _ (der_29942 v h) (by intro d hd; cases hd)))
def cl_29947 : CNF.NClause := [(88,true),(21,false),(29,true),(17,false)]
theorem der_29947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29947 :=
  CNF.rup_sound cl_29947 [cl_23498,cl_29946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23498 v h) (hints_cons _ _ _ (der_29946 v h) (by intro d hd; cases hd)))
def cl_29948 : CNF.NClause := [(79,true),(15,false),(2,true),(26,false),(8,false)]
theorem der_29948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29948 :=
  CNF.rup_sound cl_29948 [cl_23504,cl_29816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23504 v h) (hints_cons _ _ _ (der_29816 v h) (by intro d hd; cases hd)))
def cl_29949 : CNF.NClause := [(79,true),(14,false),(26,false),(2,true),(8,false)]
theorem der_29949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29949 :=
  CNF.rup_sound cl_29949 [cl_23506,cl_29948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23506 v h) (hints_cons _ _ _ (der_29948 v h) (by intro d hd; cases hd)))
def cl_29950 : CNF.NClause := [(26,false),(8,false),(79,true),(15,true),(2,true)]
theorem der_29950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29950 :=
  CNF.rup_sound cl_29950 [cl_23507,cl_29949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23507 v h) (hints_cons _ _ _ (der_29949 v h) (by intro d hd; cases hd)))
def cl_29953 : CNF.NClause := [(79,true),(21,false),(14,true),(2,true),(8,false)]
theorem der_29953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29953 :=
  CNF.rup_sound cl_29953 [cl_23511,cl_29817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23511 v h) (hints_cons _ _ _ (der_29817 v h) (by intro d hd; cases hd)))
def cl_29954 : CNF.NClause := [(79,true),(21,true),(15,false),(2,true),(8,false)]
theorem der_29954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29954 :=
  CNF.rup_sound cl_29954 [cl_23512,cl_29817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23512 v h) (hints_cons _ _ _ (der_29817 v h) (by intro d hd; cases hd)))
def cl_29955 : CNF.NClause := [(79,true),(14,false),(2,true),(15,true),(8,false)]
theorem der_29955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29955 :=
  CNF.rup_sound cl_29955 [cl_23514,cl_29950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23514 v h) (hints_cons _ _ _ (der_29950 v h) (by intro d hd; cases hd)))
def cl_29957 : CNF.NClause := [(68,true),(8,false),(12,true),(20,false),(4,false)]
theorem der_29957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29957 :=
  CNF.rup_sound cl_29957 [cl_23519,cl_23518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23519 v h) (hints_cons _ _ _ (der_23518 v h) (by intro d hd; cases hd)))
def cl_29958 : CNF.NClause := [(68,true),(16,false),(4,false),(8,false),(12,true)]
theorem der_29958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29958 :=
  CNF.rup_sound cl_29958 [cl_23520,cl_23518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23520 v h) (hints_cons _ _ _ (der_23518 v h) (by intro d hd; cases hd)))
def cl_29959 : CNF.NClause := [(68,true),(12,true),(16,true),(4,false),(8,false)]
theorem der_29959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29959 :=
  CNF.rup_sound cl_29959 [cl_23521,cl_29957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23521 v h) (hints_cons _ _ _ (der_29957 v h) (by intro d hd; cases hd)))
def chunk014 : List CNF.NClause := [cl_29370,cl_29371,cl_29372,cl_29373,cl_29374,cl_29375,cl_29376,cl_29377,cl_29379,cl_29380,cl_29381,cl_29382,cl_29383,cl_29384,cl_29385,cl_29386,cl_29387,cl_29388,cl_29389,cl_29390,cl_29391,cl_29392,cl_29393,cl_29394,cl_29395,cl_29396,cl_29397,cl_29398,cl_29399,cl_29400,cl_29401,cl_29402,cl_29403,cl_29404,cl_29405,cl_29406,cl_29407,cl_29408,cl_29409,cl_29410,cl_29411,cl_29412,cl_29413,cl_29414,cl_29415,cl_29416,cl_29417,cl_29418,cl_29419,cl_29420,cl_29421,cl_29422,cl_29423,cl_29424,cl_29425,cl_29426,cl_29427,cl_29428,cl_29429,cl_29430,cl_29431,cl_29432,cl_29433,cl_29434,cl_29435,cl_29436,cl_29437,cl_29438,cl_29439,cl_29440,cl_29441,cl_29442,cl_29443,cl_29444,cl_29445,cl_29446,cl_29447,cl_29448,cl_29449,cl_29450,cl_29451,cl_29452,cl_29453,cl_29454,cl_29455,cl_29456,cl_29457,cl_29458,cl_29459,cl_29460,cl_29461,cl_29462,cl_29463,cl_29464,cl_29465,cl_29466,cl_29467,cl_29468,cl_29469,cl_29470,cl_29471,cl_29472,cl_29473,cl_29474,cl_29475,cl_29476,cl_29477,cl_29478,cl_29479,cl_29480,cl_29481,cl_29482,cl_29483,cl_29484,cl_29485,cl_29486,cl_29487,cl_29488,cl_29489,cl_29490,cl_29491,cl_29492,cl_29493,cl_29494,cl_29495,cl_29496,cl_29497,cl_29498,cl_29499,cl_29500,cl_29501,cl_29502,cl_29503,cl_29504,cl_29505,cl_29506,cl_29507,cl_29508,cl_29509,cl_29510,cl_29511,cl_29512,cl_29513,cl_29514,cl_29515,cl_29516,cl_29517,cl_29518,cl_29519,cl_29520,cl_29521,cl_29522,cl_29523,cl_29524,cl_29525,cl_29527,cl_29528,cl_29530,cl_29531,cl_29532,cl_29533,cl_29534,cl_29535,cl_29536,cl_29537,cl_29538,cl_29539,cl_29540,cl_29541,cl_29542,cl_29543,cl_29544,cl_29545,cl_29546,cl_29547,cl_29548,cl_29549,cl_29550,cl_29551,cl_29552,cl_29553,cl_29554,cl_29555,cl_29556,cl_29557,cl_29560,cl_29561,cl_29563,cl_29564,cl_29565,cl_29568,cl_29569,cl_29570,cl_29571,cl_29572,cl_29573,cl_29574,cl_29575,cl_29576,cl_29577,cl_29578,cl_29579,cl_29580,cl_29581,cl_29582,cl_29583,cl_29584,cl_29585,cl_29586,cl_29587,cl_29591,cl_29592,cl_29593,cl_29595,cl_29596,cl_29599,cl_29600,cl_29601,cl_29602,cl_29603,cl_29604,cl_29605,cl_29606,cl_29607,cl_29608,cl_29609,cl_29610,cl_29611,cl_29612,cl_29613,cl_29614,cl_29615,cl_29616,cl_29617,cl_29618,cl_29619,cl_29620,cl_29621,cl_29622,cl_29623,cl_29624,cl_29625,cl_29626,cl_29627,cl_29628,cl_29629,cl_29630,cl_29631,cl_29632,cl_29633,cl_29634,cl_29635,cl_29636,cl_29637,cl_29638,cl_29639,cl_29640,cl_29641,cl_29642,cl_29643,cl_29644,cl_29645,cl_29646,cl_29647,cl_29648,cl_29649,cl_29650,cl_29653,cl_29654,cl_29655,cl_29656,cl_29658,cl_29661,cl_29662,cl_29663,cl_29664,cl_29665,cl_29666,cl_29667,cl_29668,cl_29669,cl_29670,cl_29671,cl_29672,cl_29673,cl_29674,cl_29675,cl_29676,cl_29677,cl_29678,cl_29679,cl_29680,cl_29681,cl_29682,cl_29683,cl_29684,cl_29685,cl_29686,cl_29687,cl_29688,cl_29689,cl_29690,cl_29691,cl_29692,cl_29693,cl_29694,cl_29695,cl_29698,cl_29699,cl_29765,cl_29766,cl_29767,cl_29768,cl_29769,cl_29770,cl_29771,cl_29772,cl_29773,cl_29774,cl_29775,cl_29776,cl_29777,cl_29778,cl_29779,cl_29780,cl_29781,cl_29782,cl_29783,cl_29784,cl_29785,cl_29786,cl_29787,cl_29788,cl_29789,cl_29790,cl_29791,cl_29792,cl_29793,cl_29794,cl_29795,cl_29796,cl_29797,cl_29798,cl_29799,cl_29800,cl_29801,cl_29802,cl_29803,cl_29804,cl_29805,cl_29806,cl_29807,cl_29808,cl_29809,cl_29810,cl_29811,cl_29812,cl_29813,cl_29814,cl_29815,cl_29816,cl_29817,cl_29818,cl_29819,cl_29820,cl_29821,cl_29822,cl_29823,cl_29824,cl_29825,cl_29826,cl_29827,cl_29828,cl_29829,cl_29830,cl_29831,cl_29832,cl_29833,cl_29834,cl_29835,cl_29836,cl_29837,cl_29838,cl_29839,cl_29840,cl_29841,cl_29842,cl_29843,cl_29844,cl_29845,cl_29846,cl_29847,cl_29848,cl_29849,cl_29850,cl_29851,cl_29852,cl_29853,cl_29854,cl_29855,cl_29856,cl_29857,cl_29858,cl_29859,cl_29860,cl_29861,cl_29862,cl_29863,cl_29864,cl_29865,cl_29866,cl_29867,cl_29868,cl_29869,cl_29870,cl_29871,cl_29872,cl_29873,cl_29874,cl_29875,cl_29876,cl_29877,cl_29878,cl_29879,cl_29880,cl_29881,cl_29882,cl_29883,cl_29884,cl_29885,cl_29886,cl_29887,cl_29888,cl_29889,cl_29890,cl_29891,cl_29892,cl_29893,cl_29894,cl_29895,cl_29896,cl_29897,cl_29898,cl_29899,cl_29900,cl_29901,cl_29902,cl_29903,cl_29904,cl_29905,cl_29906,cl_29907,cl_29908,cl_29909,cl_29910,cl_29911,cl_29912,cl_29913,cl_29914,cl_29915,cl_29916,cl_29917,cl_29918,cl_29919,cl_29920,cl_29921,cl_29922,cl_29923,cl_29924,cl_29925,cl_29926,cl_29927,cl_29928,cl_29929,cl_29930,cl_29931,cl_29933,cl_29934,cl_29935,cl_29936,cl_29937,cl_29938,cl_29939,cl_29940,cl_29941,cl_29942,cl_29943,cl_29944,cl_29945,cl_29946,cl_29947,cl_29948,cl_29949,cl_29950,cl_29953,cl_29954,cl_29955,cl_29957,cl_29958,cl_29959]
theorem chunk_sound014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk014, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_29370 v h) (hints_cons _ _ _ (der_29371 v h) (hints_cons _ _ _ (der_29372 v h) (hints_cons _ _ _ (der_29373 v h) (hints_cons _ _ _ (der_29374 v h) (hints_cons _ _ _ (der_29375 v h) (hints_cons _ _ _ (der_29376 v h) (hints_cons _ _ _ (der_29377 v h) (hints_cons _ _ _ (der_29379 v h) (hints_cons _ _ _ (der_29380 v h) (hints_cons _ _ _ (der_29381 v h) (hints_cons _ _ _ (der_29382 v h) (hints_cons _ _ _ (der_29383 v h) (hints_cons _ _ _ (der_29384 v h) (hints_cons _ _ _ (der_29385 v h) (hints_cons _ _ _ (der_29386 v h) (hints_cons _ _ _ (der_29387 v h) (hints_cons _ _ _ (der_29388 v h) (hints_cons _ _ _ (der_29389 v h) (hints_cons _ _ _ (der_29390 v h) (hints_cons _ _ _ (der_29391 v h) (hints_cons _ _ _ (der_29392 v h) (hints_cons _ _ _ (der_29393 v h) (hints_cons _ _ _ (der_29394 v h) (hints_cons _ _ _ (der_29395 v h) (hints_cons _ _ _ (der_29396 v h) (hints_cons _ _ _ (der_29397 v h) (hints_cons _ _ _ (der_29398 v h) (hints_cons _ _ _ (der_29399 v h) (hints_cons _ _ _ (der_29400 v h) (hints_cons _ _ _ (der_29401 v h) (hints_cons _ _ _ (der_29402 v h) (hints_cons _ _ _ (der_29403 v h) (hints_cons _ _ _ (der_29404 v h) (hints_cons _ _ _ (der_29405 v h) (hints_cons _ _ _ (der_29406 v h) (hints_cons _ _ _ (der_29407 v h) (hints_cons _ _ _ (der_29408 v h) (hints_cons _ _ _ (der_29409 v h) (hints_cons _ _ _ (der_29410 v h) (hints_cons _ _ _ (der_29411 v h) (hints_cons _ _ _ (der_29412 v h) (hints_cons _ _ _ (der_29413 v h) (hints_cons _ _ _ (der_29414 v h) (hints_cons _ _ _ (der_29415 v h) (hints_cons _ _ _ (der_29416 v h) (hints_cons _ _ _ (der_29417 v h) (hints_cons _ _ _ (der_29418 v h) (hints_cons _ _ _ (der_29419 v h) (hints_cons _ _ _ (der_29420 v h) (hints_cons _ _ _ (der_29421 v h) (hints_cons _ _ _ (der_29422 v h) (hints_cons _ _ _ (der_29423 v h) (hints_cons _ _ _ (der_29424 v h) (hints_cons _ _ _ (der_29425 v h) (hints_cons _ _ _ (der_29426 v h) (hints_cons _ _ _ (der_29427 v h) (hints_cons _ _ _ (der_29428 v h) (hints_cons _ _ _ (der_29429 v h) (hints_cons _ _ _ (der_29430 v h) (hints_cons _ _ _ (der_29431 v h) (hints_cons _ _ _ (der_29432 v h) (hints_cons _ _ _ (der_29433 v h) (hints_cons _ _ _ (der_29434 v h) (hints_cons _ _ _ (der_29435 v h) (hints_cons _ _ _ (der_29436 v h) (hints_cons _ _ _ (der_29437 v h) (hints_cons _ _ _ (der_29438 v h) (hints_cons _ _ _ (der_29439 v h) (hints_cons _ _ _ (der_29440 v h) (hints_cons _ _ _ (der_29441 v h) (hints_cons _ _ _ (der_29442 v h) (hints_cons _ _ _ (der_29443 v h) (hints_cons _ _ _ (der_29444 v h) (hints_cons _ _ _ (der_29445 v h) (hints_cons _ _ _ (der_29446 v h) (hints_cons _ _ _ (der_29447 v h) (hints_cons _ _ _ (der_29448 v h) (hints_cons _ _ _ (der_29449 v h) (hints_cons _ _ _ (der_29450 v h) (hints_cons _ _ _ (der_29451 v h) (hints_cons _ _ _ (der_29452 v h) (hints_cons _ _ _ (der_29453 v h) (hints_cons _ _ _ (der_29454 v h) (hints_cons _ _ _ (der_29455 v h) (hints_cons _ _ _ (der_29456 v h) (hints_cons _ _ _ (der_29457 v h) (hints_cons _ _ _ (der_29458 v h) (hints_cons _ _ _ (der_29459 v h) (hints_cons _ _ _ (der_29460 v h) (hints_cons _ _ _ (der_29461 v h) (hints_cons _ _ _ (der_29462 v h) (hints_cons _ _ _ (der_29463 v h) (hints_cons _ _ _ (der_29464 v h) (hints_cons _ _ _ (der_29465 v h) (hints_cons _ _ _ (der_29466 v h) (hints_cons _ _ _ (der_29467 v h) (hints_cons _ _ _ (der_29468 v h) (hints_cons _ _ _ (der_29469 v h) (hints_cons _ _ _ (der_29470 v h) (hints_cons _ _ _ (der_29471 v h) (hints_cons _ _ _ (der_29472 v h) (hints_cons _ _ _ (der_29473 v h) (hints_cons _ _ _ (der_29474 v h) (hints_cons _ _ _ (der_29475 v h) (hints_cons _ _ _ (der_29476 v h) (hints_cons _ _ _ (der_29477 v h) (hints_cons _ _ _ (der_29478 v h) (hints_cons _ _ _ (der_29479 v h) (hints_cons _ _ _ (der_29480 v h) (hints_cons _ _ _ (der_29481 v h) (hints_cons _ _ _ (der_29482 v h) (hints_cons _ _ _ (der_29483 v h) (hints_cons _ _ _ (der_29484 v h) (hints_cons _ _ _ (der_29485 v h) (hints_cons _ _ _ (der_29486 v h) (hints_cons _ _ _ (der_29487 v h) (hints_cons _ _ _ (der_29488 v h) (hints_cons _ _ _ (der_29489 v h) (hints_cons _ _ _ (der_29490 v h) (hints_cons _ _ _ (der_29491 v h) (hints_cons _ _ _ (der_29492 v h) (hints_cons _ _ _ (der_29493 v h) (hints_cons _ _ _ (der_29494 v h) (hints_cons _ _ _ (der_29495 v h) (hints_cons _ _ _ (der_29496 v h) (hints_cons _ _ _ (der_29497 v h) (hints_cons _ _ _ (der_29498 v h) (hints_cons _ _ _ (der_29499 v h) (hints_cons _ _ _ (der_29500 v h) (hints_cons _ _ _ (der_29501 v h) (hints_cons _ _ _ (der_29502 v h) (hints_cons _ _ _ (der_29503 v h) (hints_cons _ _ _ (der_29504 v h) (hints_cons _ _ _ (der_29505 v h) (hints_cons _ _ _ (der_29506 v h) (hints_cons _ _ _ (der_29507 v h) (hints_cons _ _ _ (der_29508 v h) (hints_cons _ _ _ (der_29509 v h) (hints_cons _ _ _ (der_29510 v h) (hints_cons _ _ _ (der_29511 v h) (hints_cons _ _ _ (der_29512 v h) (hints_cons _ _ _ (der_29513 v h) (hints_cons _ _ _ (der_29514 v h) (hints_cons _ _ _ (der_29515 v h) (hints_cons _ _ _ (der_29516 v h) (hints_cons _ _ _ (der_29517 v h) (hints_cons _ _ _ (der_29518 v h) (hints_cons _ _ _ (der_29519 v h) (hints_cons _ _ _ (der_29520 v h) (hints_cons _ _ _ (der_29521 v h) (hints_cons _ _ _ (der_29522 v h) (hints_cons _ _ _ (der_29523 v h) (hints_cons _ _ _ (der_29524 v h) (hints_cons _ _ _ (der_29525 v h) (hints_cons _ _ _ (der_29527 v h) (hints_cons _ _ _ (der_29528 v h) (hints_cons _ _ _ (der_29530 v h) (hints_cons _ _ _ (der_29531 v h) (hints_cons _ _ _ (der_29532 v h) (hints_cons _ _ _ (der_29533 v h) (hints_cons _ _ _ (der_29534 v h) (hints_cons _ _ _ (der_29535 v h) (hints_cons _ _ _ (der_29536 v h) (hints_cons _ _ _ (der_29537 v h) (hints_cons _ _ _ (der_29538 v h) (hints_cons _ _ _ (der_29539 v h) (hints_cons _ _ _ (der_29540 v h) (hints_cons _ _ _ (der_29541 v h) (hints_cons _ _ _ (der_29542 v h) (hints_cons _ _ _ (der_29543 v h) (hints_cons _ _ _ (der_29544 v h) (hints_cons _ _ _ (der_29545 v h) (hints_cons _ _ _ (der_29546 v h) (hints_cons _ _ _ (der_29547 v h) (hints_cons _ _ _ (der_29548 v h) (hints_cons _ _ _ (der_29549 v h) (hints_cons _ _ _ (der_29550 v h) (hints_cons _ _ _ (der_29551 v h) (hints_cons _ _ _ (der_29552 v h) (hints_cons _ _ _ (der_29553 v h) (hints_cons _ _ _ (der_29554 v h) (hints_cons _ _ _ (der_29555 v h) (hints_cons _ _ _ (der_29556 v h) (hints_cons _ _ _ (der_29557 v h) (hints_cons _ _ _ (der_29560 v h) (hints_cons _ _ _ (der_29561 v h) (hints_cons _ _ _ (der_29563 v h) (hints_cons _ _ _ (der_29564 v h) (hints_cons _ _ _ (der_29565 v h) (hints_cons _ _ _ (der_29568 v h) (hints_cons _ _ _ (der_29569 v h) (hints_cons _ _ _ (der_29570 v h) (hints_cons _ _ _ (der_29571 v h) (hints_cons _ _ _ (der_29572 v h) (hints_cons _ _ _ (der_29573 v h) (hints_cons _ _ _ (der_29574 v h) (hints_cons _ _ _ (der_29575 v h) (hints_cons _ _ _ (der_29576 v h) (hints_cons _ _ _ (der_29577 v h) (hints_cons _ _ _ (der_29578 v h) (hints_cons _ _ _ (der_29579 v h) (hints_cons _ _ _ (der_29580 v h) (hints_cons _ _ _ (der_29581 v h) (hints_cons _ _ _ (der_29582 v h) (hints_cons _ _ _ (der_29583 v h) (hints_cons _ _ _ (der_29584 v h) (hints_cons _ _ _ (der_29585 v h) (hints_cons _ _ _ (der_29586 v h) (hints_cons _ _ _ (der_29587 v h) (hints_cons _ _ _ (der_29591 v h) (hints_cons _ _ _ (der_29592 v h) (hints_cons _ _ _ (der_29593 v h) (hints_cons _ _ _ (der_29595 v h) (hints_cons _ _ _ (der_29596 v h) (hints_cons _ _ _ (der_29599 v h) (hints_cons _ _ _ (der_29600 v h) (hints_cons _ _ _ (der_29601 v h) (hints_cons _ _ _ (der_29602 v h) (hints_cons _ _ _ (der_29603 v h) (hints_cons _ _ _ (der_29604 v h) (hints_cons _ _ _ (der_29605 v h) (hints_cons _ _ _ (der_29606 v h) (hints_cons _ _ _ (der_29607 v h) (hints_cons _ _ _ (der_29608 v h) (hints_cons _ _ _ (der_29609 v h) (hints_cons _ _ _ (der_29610 v h) (hints_cons _ _ _ (der_29611 v h) (hints_cons _ _ _ (der_29612 v h) (hints_cons _ _ _ (der_29613 v h) (hints_cons _ _ _ (der_29614 v h) (hints_cons _ _ _ (der_29615 v h) (hints_cons _ _ _ (der_29616 v h) (hints_cons _ _ _ (der_29617 v h) (hints_cons _ _ _ (der_29618 v h) (hints_cons _ _ _ (der_29619 v h) (hints_cons _ _ _ (der_29620 v h) (hints_cons _ _ _ (der_29621 v h) (hints_cons _ _ _ (der_29622 v h) (hints_cons _ _ _ (der_29623 v h) (hints_cons _ _ _ (der_29624 v h) (hints_cons _ _ _ (der_29625 v h) (hints_cons _ _ _ (der_29626 v h) (hints_cons _ _ _ (der_29627 v h) (hints_cons _ _ _ (der_29628 v h) (hints_cons _ _ _ (der_29629 v h) (hints_cons _ _ _ (der_29630 v h) (hints_cons _ _ _ (der_29631 v h) (hints_cons _ _ _ (der_29632 v h) (hints_cons _ _ _ (der_29633 v h) (hints_cons _ _ _ (der_29634 v h) (hints_cons _ _ _ (der_29635 v h) (hints_cons _ _ _ (der_29636 v h) (hints_cons _ _ _ (der_29637 v h) (hints_cons _ _ _ (der_29638 v h) (hints_cons _ _ _ (der_29639 v h) (hints_cons _ _ _ (der_29640 v h) (hints_cons _ _ _ (der_29641 v h) (hints_cons _ _ _ (der_29642 v h) (hints_cons _ _ _ (der_29643 v h) (hints_cons _ _ _ (der_29644 v h) (hints_cons _ _ _ (der_29645 v h) (hints_cons _ _ _ (der_29646 v h) (hints_cons _ _ _ (der_29647 v h) (hints_cons _ _ _ (der_29648 v h) (hints_cons _ _ _ (der_29649 v h) (hints_cons _ _ _ (der_29650 v h) (hints_cons _ _ _ (der_29653 v h) (hints_cons _ _ _ (der_29654 v h) (hints_cons _ _ _ (der_29655 v h) (hints_cons _ _ _ (der_29656 v h) (hints_cons _ _ _ (der_29658 v h) (hints_cons _ _ _ (der_29661 v h) (hints_cons _ _ _ (der_29662 v h) (hints_cons _ _ _ (der_29663 v h) (hints_cons _ _ _ (der_29664 v h) (hints_cons _ _ _ (der_29665 v h) (hints_cons _ _ _ (der_29666 v h) (hints_cons _ _ _ (der_29667 v h) (hints_cons _ _ _ (der_29668 v h) (hints_cons _ _ _ (der_29669 v h) (hints_cons _ _ _ (der_29670 v h) (hints_cons _ _ _ (der_29671 v h) (hints_cons _ _ _ (der_29672 v h) (hints_cons _ _ _ (der_29673 v h) (hints_cons _ _ _ (der_29674 v h) (hints_cons _ _ _ (der_29675 v h) (hints_cons _ _ _ (der_29676 v h) (hints_cons _ _ _ (der_29677 v h) (hints_cons _ _ _ (der_29678 v h) (hints_cons _ _ _ (der_29679 v h) (hints_cons _ _ _ (der_29680 v h) (hints_cons _ _ _ (der_29681 v h) (hints_cons _ _ _ (der_29682 v h) (hints_cons _ _ _ (der_29683 v h) (hints_cons _ _ _ (der_29684 v h) (hints_cons _ _ _ (der_29685 v h) (hints_cons _ _ _ (der_29686 v h) (hints_cons _ _ _ (der_29687 v h) (hints_cons _ _ _ (der_29688 v h) (hints_cons _ _ _ (der_29689 v h) (hints_cons _ _ _ (der_29690 v h) (hints_cons _ _ _ (der_29691 v h) (hints_cons _ _ _ (der_29692 v h) (hints_cons _ _ _ (der_29693 v h) (hints_cons _ _ _ (der_29694 v h) (hints_cons _ _ _ (der_29695 v h) (hints_cons _ _ _ (der_29698 v h) (hints_cons _ _ _ (der_29699 v h) (hints_cons _ _ _ (der_29765 v h) (hints_cons _ _ _ (der_29766 v h) (hints_cons _ _ _ (der_29767 v h) (hints_cons _ _ _ (der_29768 v h) (hints_cons _ _ _ (der_29769 v h) (hints_cons _ _ _ (der_29770 v h) (hints_cons _ _ _ (der_29771 v h) (hints_cons _ _ _ (der_29772 v h) (hints_cons _ _ _ (der_29773 v h) (hints_cons _ _ _ (der_29774 v h) (hints_cons _ _ _ (der_29775 v h) (hints_cons _ _ _ (der_29776 v h) (hints_cons _ _ _ (der_29777 v h) (hints_cons _ _ _ (der_29778 v h) (hints_cons _ _ _ (der_29779 v h) (hints_cons _ _ _ (der_29780 v h) (hints_cons _ _ _ (der_29781 v h) (hints_cons _ _ _ (der_29782 v h) (hints_cons _ _ _ (der_29783 v h) (hints_cons _ _ _ (der_29784 v h) (hints_cons _ _ _ (der_29785 v h) (hints_cons _ _ _ (der_29786 v h) (hints_cons _ _ _ (der_29787 v h) (hints_cons _ _ _ (der_29788 v h) (hints_cons _ _ _ (der_29789 v h) (hints_cons _ _ _ (der_29790 v h) (hints_cons _ _ _ (der_29791 v h) (hints_cons _ _ _ (der_29792 v h) (hints_cons _ _ _ (der_29793 v h) (hints_cons _ _ _ (der_29794 v h) (hints_cons _ _ _ (der_29795 v h) (hints_cons _ _ _ (der_29796 v h) (hints_cons _ _ _ (der_29797 v h) (hints_cons _ _ _ (der_29798 v h) (hints_cons _ _ _ (der_29799 v h) (hints_cons _ _ _ (der_29800 v h) (hints_cons _ _ _ (der_29801 v h) (hints_cons _ _ _ (der_29802 v h) (hints_cons _ _ _ (der_29803 v h) (hints_cons _ _ _ (der_29804 v h) (hints_cons _ _ _ (der_29805 v h) (hints_cons _ _ _ (der_29806 v h) (hints_cons _ _ _ (der_29807 v h) (hints_cons _ _ _ (der_29808 v h) (hints_cons _ _ _ (der_29809 v h) (hints_cons _ _ _ (der_29810 v h) (hints_cons _ _ _ (der_29811 v h) (hints_cons _ _ _ (der_29812 v h) (hints_cons _ _ _ (der_29813 v h) (hints_cons _ _ _ (der_29814 v h) (hints_cons _ _ _ (der_29815 v h) (hints_cons _ _ _ (der_29816 v h) (hints_cons _ _ _ (der_29817 v h) (hints_cons _ _ _ (der_29818 v h) (hints_cons _ _ _ (der_29819 v h) (hints_cons _ _ _ (der_29820 v h) (hints_cons _ _ _ (der_29821 v h) (hints_cons _ _ _ (der_29822 v h) (hints_cons _ _ _ (der_29823 v h) (hints_cons _ _ _ (der_29824 v h) (hints_cons _ _ _ (der_29825 v h) (hints_cons _ _ _ (der_29826 v h) (hints_cons _ _ _ (der_29827 v h) (hints_cons _ _ _ (der_29828 v h) (hints_cons _ _ _ (der_29829 v h) (hints_cons _ _ _ (der_29830 v h) (hints_cons _ _ _ (der_29831 v h) (hints_cons _ _ _ (der_29832 v h) (hints_cons _ _ _ (der_29833 v h) (hints_cons _ _ _ (der_29834 v h) (hints_cons _ _ _ (der_29835 v h) (hints_cons _ _ _ (der_29836 v h) (hints_cons _ _ _ (der_29837 v h) (hints_cons _ _ _ (der_29838 v h) (hints_cons _ _ _ (der_29839 v h) (hints_cons _ _ _ (der_29840 v h) (hints_cons _ _ _ (der_29841 v h) (hints_cons _ _ _ (der_29842 v h) (hints_cons _ _ _ (der_29843 v h) (hints_cons _ _ _ (der_29844 v h) (hints_cons _ _ _ (der_29845 v h) (hints_cons _ _ _ (der_29846 v h) (hints_cons _ _ _ (der_29847 v h) (hints_cons _ _ _ (der_29848 v h) (hints_cons _ _ _ (der_29849 v h) (hints_cons _ _ _ (der_29850 v h) (hints_cons _ _ _ (der_29851 v h) (hints_cons _ _ _ (der_29852 v h) (hints_cons _ _ _ (der_29853 v h) (hints_cons _ _ _ (der_29854 v h) (hints_cons _ _ _ (der_29855 v h) (hints_cons _ _ _ (der_29856 v h) (hints_cons _ _ _ (der_29857 v h) (hints_cons _ _ _ (der_29858 v h) (hints_cons _ _ _ (der_29859 v h) (hints_cons _ _ _ (der_29860 v h) (hints_cons _ _ _ (der_29861 v h) (hints_cons _ _ _ (der_29862 v h) (hints_cons _ _ _ (der_29863 v h) (hints_cons _ _ _ (der_29864 v h) (hints_cons _ _ _ (der_29865 v h) (hints_cons _ _ _ (der_29866 v h) (hints_cons _ _ _ (der_29867 v h) (hints_cons _ _ _ (der_29868 v h) (hints_cons _ _ _ (der_29869 v h) (hints_cons _ _ _ (der_29870 v h) (hints_cons _ _ _ (der_29871 v h) (hints_cons _ _ _ (der_29872 v h) (hints_cons _ _ _ (der_29873 v h) (hints_cons _ _ _ (der_29874 v h) (hints_cons _ _ _ (der_29875 v h) (hints_cons _ _ _ (der_29876 v h) (hints_cons _ _ _ (der_29877 v h) (hints_cons _ _ _ (der_29878 v h) (hints_cons _ _ _ (der_29879 v h) (hints_cons _ _ _ (der_29880 v h) (hints_cons _ _ _ (der_29881 v h) (hints_cons _ _ _ (der_29882 v h) (hints_cons _ _ _ (der_29883 v h) (hints_cons _ _ _ (der_29884 v h) (hints_cons _ _ _ (der_29885 v h) (hints_cons _ _ _ (der_29886 v h) (hints_cons _ _ _ (der_29887 v h) (hints_cons _ _ _ (der_29888 v h) (hints_cons _ _ _ (der_29889 v h) (hints_cons _ _ _ (der_29890 v h) (hints_cons _ _ _ (der_29891 v h) (hints_cons _ _ _ (der_29892 v h) (hints_cons _ _ _ (der_29893 v h) (hints_cons _ _ _ (der_29894 v h) (hints_cons _ _ _ (der_29895 v h) (hints_cons _ _ _ (der_29896 v h) (hints_cons _ _ _ (der_29897 v h) (hints_cons _ _ _ (der_29898 v h) (hints_cons _ _ _ (der_29899 v h) (hints_cons _ _ _ (der_29900 v h) (hints_cons _ _ _ (der_29901 v h) (hints_cons _ _ _ (der_29902 v h) (hints_cons _ _ _ (der_29903 v h) (hints_cons _ _ _ (der_29904 v h) (hints_cons _ _ _ (der_29905 v h) (hints_cons _ _ _ (der_29906 v h) (hints_cons _ _ _ (der_29907 v h) (hints_cons _ _ _ (der_29908 v h) (hints_cons _ _ _ (der_29909 v h) (hints_cons _ _ _ (der_29910 v h) (hints_cons _ _ _ (der_29911 v h) (hints_cons _ _ _ (der_29912 v h) (hints_cons _ _ _ (der_29913 v h) (hints_cons _ _ _ (der_29914 v h) (hints_cons _ _ _ (der_29915 v h) (hints_cons _ _ _ (der_29916 v h) (hints_cons _ _ _ (der_29917 v h) (hints_cons _ _ _ (der_29918 v h) (hints_cons _ _ _ (der_29919 v h) (hints_cons _ _ _ (der_29920 v h) (hints_cons _ _ _ (der_29921 v h) (hints_cons _ _ _ (der_29922 v h) (hints_cons _ _ _ (der_29923 v h) (hints_cons _ _ _ (der_29924 v h) (hints_cons _ _ _ (der_29925 v h) (hints_cons _ _ _ (der_29926 v h) (hints_cons _ _ _ (der_29927 v h) (hints_cons _ _ _ (der_29928 v h) (hints_cons _ _ _ (der_29929 v h) (hints_cons _ _ _ (der_29930 v h) (hints_cons _ _ _ (der_29931 v h) (hints_cons _ _ _ (der_29933 v h) (hints_cons _ _ _ (der_29934 v h) (hints_cons _ _ _ (der_29935 v h) (hints_cons _ _ _ (der_29936 v h) (hints_cons _ _ _ (der_29937 v h) (hints_cons _ _ _ (der_29938 v h) (hints_cons _ _ _ (der_29939 v h) (hints_cons _ _ _ (der_29940 v h) (hints_cons _ _ _ (der_29941 v h) (hints_cons _ _ _ (der_29942 v h) (hints_cons _ _ _ (der_29943 v h) (hints_cons _ _ _ (der_29944 v h) (hints_cons _ _ _ (der_29945 v h) (hints_cons _ _ _ (der_29946 v h) (hints_cons _ _ _ (der_29947 v h) (hints_cons _ _ _ (der_29948 v h) (hints_cons _ _ _ (der_29949 v h) (hints_cons _ _ _ (der_29950 v h) (hints_cons _ _ _ (der_29953 v h) (hints_cons _ _ _ (der_29954 v h) (hints_cons _ _ _ (der_29955 v h) (hints_cons _ _ _ (der_29957 v h) (hints_cons _ _ _ (der_29958 v h) (hints_cons _ _ _ (der_29959 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix014 := prefix013 ++ chunk014
theorem prefix_sound014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix014, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound013 v h c hc
  · exact chunk_sound014 v h c hc
end Percolation.NReplay
