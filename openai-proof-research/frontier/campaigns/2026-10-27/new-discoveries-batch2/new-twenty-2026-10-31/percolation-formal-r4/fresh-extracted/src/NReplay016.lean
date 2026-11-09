import NReplay015
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_30523 : CNF.NClause := [(18,true),(21,true),(73,true),(4,false),(28,false)]
theorem der_30523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30523 :=
  CNF.rup_sound cl_30523 [cl_24469,cl_23573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24469 v h) (hints_cons _ _ _ (der_23573 v h) (by intro d hd; cases hd)))
def cl_30524 : CNF.NClause := [(73,true),(4,false),(18,false),(7,false),(21,false)]
theorem der_30524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30524 :=
  CNF.rup_sound cl_30524 [cl_24470,cl_30006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24470 v h) (hints_cons _ _ _ (der_30006 v h) (by intro d hd; cases hd)))
def cl_30525 : CNF.NClause := [(73,true),(21,false),(4,false),(18,true),(7,false)]
theorem der_30525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30525 :=
  CNF.rup_sound cl_30525 [cl_24471,cl_29996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24471 v h) (hints_cons _ _ _ (der_29996 v h) (by intro d hd; cases hd)))
def cl_30526 : CNF.NClause := [(73,true),(28,true),(21,true),(18,false),(7,false)]
theorem der_30526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30526 :=
  CNF.rup_sound cl_30526 [cl_24472,cl_30513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24472 v h) (hints_cons _ _ _ (der_30513 v h) (by intro d hd; cases hd)))
def cl_30527 : CNF.NClause := [(18,true),(7,false),(21,true),(73,true),(4,false)]
theorem der_30527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30527 :=
  CNF.rup_sound cl_30527 [cl_24473,cl_30002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24473 v h) (hints_cons _ _ _ (der_30002 v h) (by intro d hd; cases hd)))
def cl_30528 : CNF.NClause := [(76,true),(24,false),(17,false),(27,false),(8,false)]
theorem der_30528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30528 :=
  CNF.rup_sound cl_30528 [cl_24474,cl_30290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24474 v h) (hints_cons _ _ _ (der_30290 v h) (by intro d hd; cases hd)))
def cl_30530 : CNF.NClause := [(76,true),(17,false),(27,false),(1,false),(8,false)]
theorem der_30530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30530 :=
  CNF.rup_sound cl_30530 [cl_24476,cl_30528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24476 v h) (hints_cons _ _ _ (der_30528 v h) (by intro d hd; cases hd)))
def cl_30531 : CNF.NClause := [(76,true),(27,false),(17,true),(10,true),(8,false)]
theorem der_30531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30531 :=
  CNF.rup_sound cl_30531 [cl_24477,cl_30293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24477 v h) (hints_cons _ _ _ (der_30293 v h) (by intro d hd; cases hd)))
def cl_30533 : CNF.NClause := [(76,true),(10,true),(17,true),(24,false),(8,false)]
theorem der_30533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30533 :=
  CNF.rup_sound cl_30533 [cl_24479,cl_30297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24479 v h) (hints_cons _ _ _ (der_30297 v h) (by intro d hd; cases hd)))
def cl_30534 : CNF.NClause := [(76,true),(10,true),(27,true),(17,false),(1,false)]
theorem der_30534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30534 :=
  CNF.rup_sound cl_30534 [cl_24480,cl_30155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24480 v h) (hints_cons _ _ _ (der_30155 v h) (by intro d hd; cases hd)))
def cl_30535 : CNF.NClause := [(75,true),(16,true),(26,false),(9,false),(22,false)]
theorem der_30535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30535 :=
  CNF.rup_sound cl_30535 [cl_24483,cl_30029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24483 v h) (hints_cons _ _ _ (der_30029 v h) (by intro d hd; cases hd)))
def cl_30536 : CNF.NClause := [(75,true),(3,false),(26,false),(9,false),(16,false)]
theorem der_30536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30536 :=
  CNF.rup_sound cl_30536 [cl_24484,cl_23636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24484 v h) (hints_cons _ _ _ (der_23636 v h) (by intro d hd; cases hd)))
def cl_30537 : CNF.NClause := [(22,true),(9,false),(26,false),(3,false),(75,true)]
theorem der_30537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30537 :=
  CNF.rup_sound cl_30537 [cl_24485,cl_30536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24485 v h) (hints_cons _ _ _ (der_30536 v h) (by intro d hd; cases hd)))
def cl_30538 : CNF.NClause := [(9,false),(75,true),(3,false),(22,false),(16,false)]
theorem der_30538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30538 :=
  CNF.rup_sound cl_30538 [cl_24486,cl_24482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24486 v h) (hints_cons _ _ _ (der_24482 v h) (by intro d hd; cases hd)))
def cl_30539 : CNF.NClause := [(75,true),(3,false),(16,true),(9,false),(22,false)]
theorem der_30539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30539 :=
  CNF.rup_sound cl_30539 [cl_24487,cl_30535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24487 v h) (hints_cons _ _ _ (der_30535 v h) (by intro d hd; cases hd)))
def cl_30540 : CNF.NClause := [(75,true),(3,false),(22,true),(9,false),(16,false)]
theorem der_30540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30540 :=
  CNF.rup_sound cl_30540 [cl_24488,cl_30536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24488 v h) (hints_cons _ _ _ (der_30536 v h) (by intro d hd; cases hd)))
def cl_30541 : CNF.NClause := [(75,true),(22,true),(16,true),(3,false),(9,false)]
theorem der_30541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30541 :=
  CNF.rup_sound cl_30541 [cl_24489,cl_30537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24489 v h) (hints_cons _ _ _ (der_30537 v h) (by intro d hd; cases hd)))
def cl_30542 : CNF.NClause := [(74,true),(6,true),(23,false),(19,false),(29,false)]
theorem der_30542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30542 :=
  CNF.rup_sound cl_30542 [cl_24490,cl_30162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24490 v h) (hints_cons _ _ _ (der_30162 v h) (by intro d hd; cases hd)))
def cl_30543 : CNF.NClause := [(74,true),(2,true),(6,true),(19,false),(29,false)]
theorem der_30543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30543 :=
  CNF.rup_sound cl_30543 [cl_24491,cl_30542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24491 v h) (hints_cons _ _ _ (der_30542 v h) (by intro d hd; cases hd)))
def cl_30544 : CNF.NClause := [(74,true),(29,true),(19,false),(23,false),(2,true)]
theorem der_30544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30544 :=
  CNF.rup_sound cl_30544 [cl_24492,cl_30189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24492 v h) (hints_cons _ _ _ (der_30189 v h) (by intro d hd; cases hd)))
def cl_30545 : CNF.NClause := [(73,true),(21,false),(4,false),(28,false),(18,false)]
theorem der_30545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30545 :=
  CNF.rup_sound cl_30545 [cl_24493,cl_30520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24493 v h) (hints_cons _ _ _ (der_30520 v h) (by intro d hd; cases hd)))
def cl_30546 : CNF.NClause := [(21,true),(7,true),(73,true),(4,false),(28,false)]
theorem der_30546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30546 :=
  CNF.rup_sound cl_30546 [cl_24494,cl_23573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24494 v h) (hints_cons _ _ _ (der_23573 v h) (by intro d hd; cases hd)))
def cl_30547 : CNF.NClause := [(73,true),(10,true),(21,false),(4,false),(7,true)]
theorem der_30547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30547 :=
  CNF.rup_sound cl_30547 [cl_24495,cl_23574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24495 v h) (hints_cons _ _ _ (der_23574 v h) (by intro d hd; cases hd)))
def cl_30548 : CNF.NClause := [(73,true),(7,true),(18,false),(4,false),(21,true)]
theorem der_30548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30548 :=
  CNF.rup_sound cl_30548 [cl_24496,cl_30546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24496 v h) (hints_cons _ _ _ (der_30546 v h) (by intro d hd; cases hd)))
def cl_30549 : CNF.NClause := [(3,true),(75,true),(9,false),(22,false),(26,false)]
theorem der_30549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30549 :=
  CNF.rup_sound cl_30549 [cl_24497,cl_30535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24497 v h) (hints_cons _ _ _ (der_30535 v h) (by intro d hd; cases hd)))
def cl_30550 : CNF.NClause := [(16,false),(26,false),(75,true),(9,false),(22,true)]
theorem der_30550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30550 :=
  CNF.rup_sound cl_30550 [cl_24498,cl_30540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24498 v h) (hints_cons _ _ _ (der_30540 v h) (by intro d hd; cases hd)))
def cl_30551 : CNF.NClause := [(75,true),(3,true),(22,false),(9,false),(26,true)]
theorem der_30551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30551 :=
  CNF.rup_sound cl_30551 [cl_24499,cl_30455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24499 v h) (hints_cons _ _ _ (der_30455 v h) (by intro d hd; cases hd)))
def cl_30552 : CNF.NClause := [(74,true),(10,true),(6,true),(23,false),(29,false)]
theorem der_30552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30552 :=
  CNF.rup_sound cl_30552 [cl_24501,cl_30542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24501 v h) (hints_cons _ _ _ (der_30542 v h) (by intro d hd; cases hd)))
def cl_30553 : CNF.NClause := [(73,true),(10,true),(28,false),(18,false),(21,false)]
theorem der_30553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30553 :=
  CNF.rup_sound cl_30553 [cl_24502,cl_30545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24502 v h) (hints_cons _ _ _ (der_30545 v h) (by intro d hd; cases hd)))
def cl_30554 : CNF.NClause := [(73,true),(10,true),(4,true),(21,false),(28,false)]
theorem der_30554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30554 :=
  CNF.rup_sound cl_30554 [cl_24503,cl_30553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24503 v h) (hints_cons _ _ _ (der_30553 v h) (by intro d hd; cases hd)))
def cl_30555 : CNF.NClause := [(73,true),(10,true),(4,true),(28,false),(18,false)]
theorem der_30555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30555 :=
  CNF.rup_sound cl_30555 [cl_24504,cl_30553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24504 v h) (hints_cons _ _ _ (der_30553 v h) (by intro d hd; cases hd)))
def cl_30556 : CNF.NClause := [(73,true),(10,true),(21,false),(18,false),(7,true)]
theorem der_30556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30556 :=
  CNF.rup_sound cl_30556 [cl_24505,cl_30553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24505 v h) (hints_cons _ _ _ (der_30553 v h) (by intro d hd; cases hd)))
def cl_30557 : CNF.NClause := [(10,true),(26,false),(22,false),(75,true),(9,true)]
theorem der_30557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30557 :=
  CNF.rup_sound cl_30557 [cl_24507,cl_30496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24507 v h) (hints_cons _ _ _ (der_30496 v h) (by intro d hd; cases hd)))
def cl_30558 : CNF.NClause := [(75,true),(10,true),(26,false),(9,true),(16,false)]
theorem der_30558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30558 :=
  CNF.rup_sound cl_30558 [cl_24508,cl_30498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24508 v h) (hints_cons _ _ _ (der_30498 v h) (by intro d hd; cases hd)))
def cl_30559 : CNF.NClause := [(75,true),(10,true),(9,true),(22,false),(16,false)]
theorem der_30559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30559 :=
  CNF.rup_sound cl_30559 [cl_24510,cl_30557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24510 v h) (hints_cons _ _ _ (der_30557 v h) (by intro d hd; cases hd)))
def cl_30560 : CNF.NClause := [(3,false),(26,true),(22,false),(75,true),(16,true)]
theorem der_30560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30560 :=
  CNF.rup_sound cl_30560 [cl_24511,cl_30539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24511 v h) (hints_cons _ _ _ (der_30539 v h) (by intro d hd; cases hd)))
def cl_30561 : CNF.NClause := [(74,true),(2,true),(23,false),(19,false),(6,false)]
theorem der_30561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30561 :=
  CNF.rup_sound cl_30561 [cl_24512,cl_23596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24512 v h) (hints_cons _ _ _ (der_23596 v h) (by intro d hd; cases hd)))
def cl_30562 : CNF.NClause := [(74,true),(29,false),(2,true),(19,true),(6,false)]
theorem der_30562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30562 :=
  CNF.rup_sound cl_30562 [cl_24513,cl_23552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24513 v h) (hints_cons _ _ _ (der_23552 v h) (by intro d hd; cases hd)))
def cl_30563 : CNF.NClause := [(74,true),(29,false),(2,true),(23,true),(6,false)]
theorem der_30563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30563 :=
  CNF.rup_sound cl_30563 [cl_24514,cl_23597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24514 v h) (hints_cons _ _ _ (der_23597 v h) (by intro d hd; cases hd)))
def cl_30564 : CNF.NClause := [(8,true),(24,false),(76,true),(17,false),(1,false)]
theorem der_30564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30564 :=
  CNF.rup_sound cl_30564 [cl_24515,cl_30155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24515 v h) (hints_cons _ _ _ (der_30155 v h) (by intro d hd; cases hd)))
def cl_30565 : CNF.NClause := [(76,true),(1,false),(8,true),(17,false),(24,true)]
theorem der_30565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30565 :=
  CNF.rup_sound cl_30565 [cl_24517,cl_30155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24517 v h) (hints_cons _ _ _ (der_30155 v h) (by intro d hd; cases hd)))
def cl_30566 : CNF.NClause := [(78,true),(27,false),(15,false),(13,false),(22,false)]
theorem der_30566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30566 :=
  CNF.rup_sound cl_30566 [cl_24519,cl_30191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24519 v h) (hints_cons _ _ _ (der_30191 v h) (by intro d hd; cases hd)))
def cl_30568 : CNF.NClause := [(27,true),(78,true),(15,false),(22,true),(13,false)]
theorem der_30568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30568 :=
  CNF.rup_sound cl_30568 [cl_24521,cl_30199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24521 v h) (hints_cons _ _ _ (der_30199 v h) (by intro d hd; cases hd)))
def cl_30569 : CNF.NClause := [(78,true),(27,true),(22,true),(13,false),(6,false)]
theorem der_30569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30569 :=
  CNF.rup_sound cl_30569 [cl_24523,cl_30401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24523 v h) (hints_cons _ _ _ (der_30401 v h) (by intro d hd; cases hd)))
def cl_30570 : CNF.NClause := [(68,true),(12,true),(20,false),(29,false),(16,false)]
theorem der_30570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30570 :=
  CNF.rup_sound cl_30570 [cl_24525,cl_30158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24525 v h) (hints_cons _ _ _ (der_30158 v h) (by intro d hd; cases hd)))
def cl_30572 : CNF.NClause := [(68,true),(8,false),(12,true),(20,false),(29,false)]
theorem der_30572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30572 :=
  CNF.rup_sound cl_30572 [cl_24527,cl_30570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24527 v h) (hints_cons _ _ _ (der_30570 v h) (by intro d hd; cases hd)))
def cl_30573 : CNF.NClause := [(68,true),(4,true),(29,false),(12,false),(16,false)]
theorem der_30573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30573 :=
  CNF.rup_sound cl_30573 [cl_24528,cl_30149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24528 v h) (hints_cons _ _ _ (der_30149 v h) (by intro d hd; cases hd)))
def cl_30574 : CNF.NClause := [(29,false),(68,true),(12,true),(8,false),(16,false)]
theorem der_30574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30574 :=
  CNF.rup_sound cl_30574 [cl_24529,cl_30570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24529 v h) (hints_cons _ _ _ (der_30570 v h) (by intro d hd; cases hd)))
def cl_30575 : CNF.NClause := [(4,true),(29,false),(68,true),(16,true),(12,false)]
theorem der_30575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30575 :=
  CNF.rup_sound cl_30575 [cl_24530,cl_30149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24530 v h) (hints_cons _ _ _ (der_30149 v h) (by intro d hd; cases hd)))
def cl_30576 : CNF.NClause := [(68,true),(29,false),(20,true),(12,true),(8,false)]
theorem der_30576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30576 :=
  CNF.rup_sound cl_30576 [cl_24531,cl_30574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24531 v h) (hints_cons _ _ _ (der_30574 v h) (by intro d hd; cases hd)))
def cl_30577 : CNF.NClause := [(68,true),(16,false),(20,false),(12,false),(4,true)]
theorem der_30577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30577 :=
  CNF.rup_sound cl_30577 [cl_24532,cl_24524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24532 v h) (hints_cons _ _ _ (der_24524 v h) (by intro d hd; cases hd)))
def cl_30578 : CNF.NClause := [(68,true),(16,false),(20,false),(8,false),(12,true)]
theorem der_30578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30578 :=
  CNF.rup_sound cl_30578 [cl_24533,cl_30570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24533 v h) (hints_cons _ _ _ (der_30570 v h) (by intro d hd; cases hd)))
def cl_30579 : CNF.NClause := [(68,true),(12,false),(4,true),(20,false),(8,false)]
theorem der_30579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30579 :=
  CNF.rup_sound cl_30579 [cl_24534,cl_30577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24534 v h) (hints_cons _ _ _ (der_30577 v h) (by intro d hd; cases hd)))
def cl_30580 : CNF.NClause := [(68,true),(8,false),(12,true),(20,false),(16,true)]
theorem der_30580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30580 :=
  CNF.rup_sound cl_30580 [cl_24535,cl_30572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24535 v h) (hints_cons _ _ _ (der_30572 v h) (by intro d hd; cases hd)))
def cl_30581 : CNF.NClause := [(68,true),(16,false),(29,true),(12,false),(20,true)]
theorem der_30581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30581 :=
  CNF.rup_sound cl_30581 [cl_24536,cl_30152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24536 v h) (hints_cons _ _ _ (der_30152 v h) (by intro d hd; cases hd)))
def cl_30582 : CNF.NClause := [(68,true),(16,false),(20,true),(29,true),(8,false)]
theorem der_30582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30582 :=
  CNF.rup_sound cl_30582 [cl_24537,cl_30581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24537 v h) (hints_cons _ _ _ (der_30581 v h) (by intro d hd; cases hd)))
def cl_30583 : CNF.NClause := [(68,true),(12,false),(4,true),(16,true),(8,false)]
theorem der_30583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30583 :=
  CNF.rup_sound cl_30583 [cl_24538,cl_30579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24538 v h) (hints_cons _ _ _ (der_30579 v h) (by intro d hd; cases hd)))
def cl_30584 : CNF.NClause := [(83,true),(4,true),(26,false),(17,false),(5,false)]
theorem der_30584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30584 :=
  CNF.rup_sound cl_30584 [cl_24540,cl_24539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24540 v h) (hints_cons _ _ _ (der_24539 v h) (by intro d hd; cases hd)))
def cl_30585 : CNF.NClause := [(4,true),(17,false),(26,true),(11,false),(83,true)]
theorem der_30585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30585 :=
  CNF.rup_sound cl_30585 [cl_24541,cl_30249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24541 v h) (hints_cons _ _ _ (der_30249 v h) (by intro d hd; cases hd)))
def cl_30586 : CNF.NClause := [(4,true),(17,false),(11,true),(5,false),(83,true)]
theorem der_30586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30586 :=
  CNF.rup_sound cl_30586 [cl_24542,cl_29964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24542 v h) (hints_cons _ _ _ (der_29964 v h) (by intro d hd; cases hd)))
def cl_30587 : CNF.NClause := [(23,true),(29,false),(74,true),(19,true),(6,false)]
theorem der_30587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30587 :=
  CNF.rup_sound cl_30587 [cl_24545,cl_24461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24545 v h) (hints_cons _ _ _ (der_24461 v h) (by intro d hd; cases hd)))
def cl_30588 : CNF.NClause := [(74,true),(29,true),(6,false),(10,false),(23,false)]
theorem der_30588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30588 :=
  CNF.rup_sound cl_30588 [cl_24546,cl_30370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24546 v h) (hints_cons _ _ _ (der_30370 v h) (by intro d hd; cases hd)))
def cl_30589 : CNF.NClause := [(74,true),(29,true),(2,false),(10,false),(6,false)]
theorem der_30589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30589 :=
  CNF.rup_sound cl_30589 [cl_24547,cl_30588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24547 v h) (hints_cons _ _ _ (der_30588 v h) (by intro d hd; cases hd)))
def cl_30590 : CNF.NClause := [(86,true),(29,false),(1,false),(18,false),(22,false)]
theorem der_30590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30590 :=
  CNF.rup_sound cl_30590 [cl_24548,cl_30287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24548 v h) (hints_cons _ _ _ (der_30287 v h) (by intro d hd; cases hd)))
def cl_30591 : CNF.NClause := [(28,false),(17,true),(6,true),(70,true),(20,false)]
theorem der_30591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30591 :=
  CNF.rup_sound cl_30591 [cl_24549,cl_30470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24549 v h) (hints_cons _ _ _ (der_30470 v h) (by intro d hd; cases hd)))
def cl_30592 : CNF.NClause := [(20,true),(14,false),(3,true),(70,true),(28,false)]
theorem der_30592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30592 :=
  CNF.rup_sound cl_30592 [cl_24550,cl_30474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24550 v h) (hints_cons _ _ _ (der_30474 v h) (by intro d hd; cases hd)))
def cl_30593 : CNF.NClause := [(14,false),(6,true),(17,true),(70,true),(20,false)]
theorem der_30593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30593 :=
  CNF.rup_sound cl_30593 [cl_24551,cl_30591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24551 v h) (hints_cons _ _ _ (der_30591 v h) (by intro d hd; cases hd)))
def cl_30594 : CNF.NClause := [(29,false),(14,false),(1,true),(86,true),(22,false)]
theorem der_30594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30594 :=
  CNF.rup_sound cl_30594 [cl_24552,cl_24224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24552 v h) (hints_cons _ _ _ (der_24224 v h) (by intro d hd; cases hd)))
def cl_30595 : CNF.NClause := [(86,true),(29,false),(18,true),(1,true),(14,false)]
theorem der_30595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30595 :=
  CNF.rup_sound cl_30595 [cl_24553,cl_30594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24553 v h) (hints_cons _ _ _ (der_30594 v h) (by intro d hd; cases hd)))
def cl_30596 : CNF.NClause := [(22,false),(1,true),(86,true),(18,true),(14,false)]
theorem der_30596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30596 :=
  CNF.rup_sound cl_30596 [cl_24554,cl_30594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24554 v h) (hints_cons _ _ _ (der_30594 v h) (by intro d hd; cases hd)))
def cl_30597 : CNF.NClause := [(29,false),(18,true),(86,true),(1,false),(22,false)]
theorem der_30597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30597 :=
  CNF.rup_sound cl_30597 [cl_24555,cl_30200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24555 v h) (hints_cons _ _ _ (der_30200 v h) (by intro d hd; cases hd)))
def cl_30598 : CNF.NClause := [(22,true),(29,false),(18,true),(86,true),(5,false)]
theorem der_30598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30598 :=
  CNF.rup_sound cl_30598 [cl_24556,cl_30317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24556 v h) (hints_cons _ _ _ (der_30317 v h) (by intro d hd; cases hd)))
def cl_30599 : CNF.NClause := [(18,true),(1,false),(5,false),(86,true),(22,false)]
theorem der_30599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30599 :=
  CNF.rup_sound cl_30599 [cl_24557,cl_30597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24557 v h) (hints_cons _ _ _ (der_30597 v h) (by intro d hd; cases hd)))
def cl_30600 : CNF.NClause := [(1,false),(5,false),(18,true),(86,true),(29,true)]
theorem der_30600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30600 :=
  CNF.rup_sound cl_30600 [cl_24558,cl_30599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24558 v h) (hints_cons _ _ _ (der_30599 v h) (by intro d hd; cases hd)))
def cl_30601 : CNF.NClause := [(29,false),(5,false),(22,true),(86,true),(1,false)]
theorem der_30601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30601 :=
  CNF.rup_sound cl_30601 [cl_24559,cl_30598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24559 v h) (hints_cons _ _ _ (der_30598 v h) (by intro d hd; cases hd)))
def cl_30602 : CNF.NClause := [(76,true),(17,true),(10,true),(24,false),(27,false)]
theorem der_30602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30602 :=
  CNF.rup_sound cl_30602 [cl_24560,cl_24516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24560 v h) (hints_cons _ _ _ (der_24516 v h) (by intro d hd; cases hd)))
def cl_30603 : CNF.NClause := [(83,true),(5,true),(17,true),(4,false),(26,false)]
theorem der_30603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30603 :=
  CNF.rup_sound cl_30603 [cl_24562,cl_24561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24562 v h) (hints_cons _ _ _ (der_24561 v h) (by intro d hd; cases hd)))
def cl_30604 : CNF.NClause := [(83,true),(23,false),(26,true),(5,true),(4,false)]
theorem der_30604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30604 :=
  CNF.rup_sound cl_30604 [cl_24563,cl_30341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24563 v h) (hints_cons _ _ _ (der_30341 v h) (by intro d hd; cases hd)))
def cl_30605 : CNF.NClause := [(76,true),(10,false),(24,false),(27,false),(8,false)]
theorem der_30605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30605 :=
  CNF.rup_sound cl_30605 [cl_24564,cl_30290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24564 v h) (hints_cons _ _ _ (der_30290 v h) (by intro d hd; cases hd)))
def cl_30606 : CNF.NClause := [(27,false),(10,false),(8,false),(76,true),(17,true)]
theorem der_30606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30606 :=
  CNF.rup_sound cl_30606 [cl_24565,cl_30605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24565 v h) (hints_cons _ _ _ (der_30605 v h) (by intro d hd; cases hd)))
def cl_30607 : CNF.NClause := [(10,false),(24,false),(76,true),(1,false),(8,false)]
theorem der_30607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30607 :=
  CNF.rup_sound cl_30607 [cl_24566,cl_30605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24566 v h) (hints_cons _ _ _ (der_30605 v h) (by intro d hd; cases hd)))
def cl_30608 : CNF.NClause := [(83,true),(26,false),(4,false),(11,false),(23,false)]
theorem der_30608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30608 :=
  CNF.rup_sound cl_30608 [cl_24568,cl_24121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24568 v h) (hints_cons _ _ _ (der_24121 v h) (by intro d hd; cases hd)))
def cl_30609 : CNF.NClause := [(83,true),(23,true),(4,false),(11,false),(26,false)]
theorem der_30609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30609 :=
  CNF.rup_sound cl_30609 [cl_24569,cl_30246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24569 v h) (hints_cons _ _ _ (der_30246 v h) (by intro d hd; cases hd)))
def cl_30610 : CNF.NClause := [(5,false),(4,false),(23,false),(11,false),(83,true)]
theorem der_30610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30610 :=
  CNF.rup_sound cl_30610 [cl_24570,cl_30608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24570 v h) (hints_cons _ _ _ (der_30608 v h) (by intro d hd; cases hd)))
def cl_30611 : CNF.NClause := [(83,true),(23,true),(4,false),(5,false),(17,true)]
theorem der_30611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30611 :=
  CNF.rup_sound cl_30611 [cl_24571,cl_30429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24571 v h) (hints_cons _ _ _ (der_30429 v h) (by intro d hd; cases hd)))
def cl_30612 : CNF.NClause := [(20,true),(6,false),(3,false),(14,true),(70,true)]
theorem der_30612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30612 :=
  CNF.rup_sound cl_30612 [cl_24572,cl_30285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24572 v h) (hints_cons _ _ _ (der_30285 v h) (by intro d hd; cases hd)))
def cl_30613 : CNF.NClause := [(4,true),(23,false),(26,false),(5,false),(83,true)]
theorem der_30613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30613 :=
  CNF.rup_sound cl_30613 [cl_24573,cl_24539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24573 v h) (hints_cons _ _ _ (der_24539 v h) (by intro d hd; cases hd)))
def cl_30614 : CNF.NClause := [(23,true),(83,true),(17,true),(26,false),(5,false)]
theorem der_30614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30614 :=
  CNF.rup_sound cl_30614 [cl_24574,cl_30611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24574 v h) (hints_cons _ _ _ (der_30611 v h) (by intro d hd; cases hd)))
def cl_30615 : CNF.NClause := [(4,true),(23,false),(5,false),(11,false),(83,true)]
theorem der_30615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30615 :=
  CNF.rup_sound cl_30615 [cl_24575,cl_30613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24575 v h) (hints_cons _ _ _ (der_30613 v h) (by intro d hd; cases hd)))
def cl_30616 : CNF.NClause := [(24,false),(10,false),(76,true),(27,false),(1,false)]
theorem der_30616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30616 :=
  CNF.rup_sound cl_30616 [cl_24576,cl_30607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24576 v h) (hints_cons _ _ _ (der_30607 v h) (by intro d hd; cases hd)))
def cl_30617 : CNF.NClause := [(76,true),(10,false),(8,true),(24,true),(1,false)]
theorem der_30617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30617 :=
  CNF.rup_sound cl_30617 [cl_24577,cl_30156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24577 v h) (hints_cons _ _ _ (der_30156 v h) (by intro d hd; cases hd)))
def cl_30618 : CNF.NClause := [(76,true),(27,false),(24,false),(10,false),(1,true)]
theorem der_30618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30618 :=
  CNF.rup_sound cl_30618 [cl_24578,cl_30290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24578 v h) (hints_cons _ _ _ (der_30290 v h) (by intro d hd; cases hd)))
def cl_30619 : CNF.NClause := [(76,true),(27,false),(10,false),(1,true),(17,true)]
theorem der_30619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30619 :=
  CNF.rup_sound cl_30619 [cl_24579,cl_30618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24579 v h) (hints_cons _ _ _ (der_30618 v h) (by intro d hd; cases hd)))
def cl_30620 : CNF.NClause := [(76,true),(27,true),(24,false),(8,true),(10,false)]
theorem der_30620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30620 :=
  CNF.rup_sound cl_30620 [cl_24580,cl_23993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24580 v h) (hints_cons _ _ _ (der_23993 v h) (by intro d hd; cases hd)))
def cl_30622 : CNF.NClause := [(70,true),(14,false),(28,false),(17,true),(6,false)]
theorem der_30622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30622 :=
  CNF.rup_sound cl_30622 [cl_24582,cl_30473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24582 v h) (hints_cons _ _ _ (der_30473 v h) (by intro d hd; cases hd)))
def cl_30623 : CNF.NClause := [(28,true),(6,false),(70,true),(20,false),(3,false)]
theorem der_30623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30623 :=
  CNF.rup_sound cl_30623 [cl_24583,cl_30507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24583 v h) (hints_cons _ _ _ (der_30507 v h) (by intro d hd; cases hd)))
def cl_30624 : CNF.NClause := [(20,true),(6,false),(28,true),(70,true),(3,false)]
theorem der_30624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30624 :=
  CNF.rup_sound cl_30624 [cl_24584,cl_24172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24584 v h) (hints_cons _ _ _ (der_24172 v h) (by intro d hd; cases hd)))
def cl_30625 : CNF.NClause := [(28,false),(24,false),(84,true),(16,false),(2,false)]
theorem der_30625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30625 :=
  CNF.rup_sound cl_30625 [cl_24586,cl_24077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24586 v h) (hints_cons _ _ _ (der_24077 v h) (by intro d hd; cases hd)))
def cl_30626 : CNF.NClause := [(16,true),(24,false),(28,false),(84,true),(2,false)]
theorem der_30626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30626 :=
  CNF.rup_sound cl_30626 [cl_24587,cl_30362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24587 v h) (hints_cons _ _ _ (der_30362 v h) (by intro d hd; cases hd)))
def cl_30628 : CNF.NClause := [(28,false),(16,true),(5,false),(84,true),(2,false)]
theorem der_30628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30628 :=
  CNF.rup_sound cl_30628 [cl_24589,cl_30626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24589 v h) (hints_cons _ _ _ (der_30626 v h) (by intro d hd; cases hd)))
def cl_30629 : CNF.NClause := [(28,true),(24,false),(84,true),(16,false),(2,false)]
theorem der_30629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30629 :=
  CNF.rup_sound cl_30629 [cl_24590,cl_30215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24590 v h) (hints_cons _ _ _ (der_30215 v h) (by intro d hd; cases hd)))
def cl_30630 : CNF.NClause := [(13,true),(24,false),(2,false),(84,true),(16,true)]
theorem der_30630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30630 :=
  CNF.rup_sound cl_30630 [cl_24591,cl_30213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24591 v h) (hints_cons _ _ _ (der_30213 v h) (by intro d hd; cases hd)))
def cl_30631 : CNF.NClause := [(84,true),(5,false),(24,true),(16,false),(2,false)]
theorem der_30631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30631 :=
  CNF.rup_sound cl_30631 [cl_24592,cl_30378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24592 v h) (hints_cons _ _ _ (der_30378 v h) (by intro d hd; cases hd)))
def cl_30632 : CNF.NClause := [(84,true),(24,true),(13,true),(5,false),(2,false)]
theorem der_30632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30632 :=
  CNF.rup_sound cl_30632 [cl_24593,cl_30631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24593 v h) (hints_cons _ _ _ (der_30631 v h) (by intro d hd; cases hd)))
def cl_30633 : CNF.NClause := [(78,true),(4,false),(27,false),(22,false),(6,false)]
theorem der_30633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30633 :=
  CNF.rup_sound cl_30633 [cl_24595,cl_24594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24595 v h) (hints_cons _ _ _ (der_24594 v h) (by intro d hd; cases hd)))
def cl_30634 : CNF.NClause := [(78,true),(15,false),(4,false),(27,false),(6,false)]
theorem der_30634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30634 :=
  CNF.rup_sound cl_30634 [cl_24596,cl_30633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24596 v h) (hints_cons _ _ _ (der_30633 v h) (by intro d hd; cases hd)))
def cl_30635 : CNF.NClause := [(78,true),(13,true),(4,false),(27,false),(6,false)]
theorem der_30635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30635 :=
  CNF.rup_sound cl_30635 [cl_24597,cl_30633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24597 v h) (hints_cons _ _ _ (der_30633 v h) (by intro d hd; cases hd)))
def cl_30636 : CNF.NClause := [(78,true),(15,false),(4,false),(22,false),(6,false)]
theorem der_30636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30636 :=
  CNF.rup_sound cl_30636 [cl_24598,cl_30348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24598 v h) (hints_cons _ _ _ (der_30348 v h) (by intro d hd; cases hd)))
def cl_30637 : CNF.NClause := [(27,true),(78,true),(4,false),(15,true),(22,false)]
theorem der_30637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30637 :=
  CNF.rup_sound cl_30637 [cl_24599,cl_30409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24599 v h) (hints_cons _ _ _ (der_30409 v h) (by intro d hd; cases hd)))
def cl_30638 : CNF.NClause := [(27,true),(78,true),(6,false),(15,false),(22,true)]
theorem der_30638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30638 :=
  CNF.rup_sound cl_30638 [cl_24600,cl_24522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24600 v h) (hints_cons _ _ _ (der_24522 v h) (by intro d hd; cases hd)))
def cl_30639 : CNF.NClause := [(78,true),(13,true),(15,true),(4,false),(6,false)]
theorem der_30639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30639 :=
  CNF.rup_sound cl_30639 [cl_24601,cl_30635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24601 v h) (hints_cons _ _ _ (der_30635 v h) (by intro d hd; cases hd)))
def cl_30640 : CNF.NClause := [(7,true),(19,false),(71,true),(26,false),(20,false)]
theorem der_30640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30640 :=
  CNF.rup_sound cl_30640 [cl_24602,cl_30332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24602 v h) (hints_cons _ _ _ (der_30332 v h) (by intro d hd; cases hd)))
def cl_30641 : CNF.NClause := [(71,true),(19,false),(7,true),(1,true),(26,false)]
theorem der_30641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30641 :=
  CNF.rup_sound cl_30641 [cl_24603,cl_30018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24603 v h) (hints_cons _ _ _ (der_30018 v h) (by intro d hd; cases hd)))
def cl_30642 : CNF.NClause := [(26,true),(19,false),(1,true),(71,true),(20,false)]
theorem der_30642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30642 :=
  CNF.rup_sound cl_30642 [cl_24604,cl_30309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24604 v h) (hints_cons _ _ _ (der_30309 v h) (by intro d hd; cases hd)))
def cl_30643 : CNF.NClause := [(5,true),(28,false),(24,false),(84,true),(16,false)]
theorem der_30643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30643 :=
  CNF.rup_sound cl_30643 [cl_24605,cl_24077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24605 v h) (hints_cons _ _ _ (der_24077 v h) (by intro d hd; cases hd)))
def cl_30644 : CNF.NClause := [(84,true),(16,false),(13,true),(28,false),(5,true)]
theorem der_30644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30644 :=
  CNF.rup_sound cl_30644 [cl_24606,cl_30208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24606 v h) (hints_cons _ _ _ (der_30208 v h) (by intro d hd; cases hd)))
def cl_30645 : CNF.NClause := [(84,true),(13,true),(5,true),(24,false),(16,false)]
theorem der_30645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30645 :=
  CNF.rup_sound cl_30645 [cl_24607,cl_30644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24607 v h) (hints_cons _ _ _ (der_30644 v h) (by intro d hd; cases hd)))
def cl_30646 : CNF.NClause := [(78,true),(27,false),(15,false),(6,true),(22,false)]
theorem der_30646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30646 :=
  CNF.rup_sound cl_30646 [cl_24608,cl_30194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24608 v h) (hints_cons _ _ _ (der_30194 v h) (by intro d hd; cases hd)))
def cl_30647 : CNF.NClause := [(78,true),(22,true),(6,true),(15,false),(27,false)]
theorem der_30647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30647 :=
  CNF.rup_sound cl_30647 [cl_24609,cl_30194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24609 v h) (hints_cons _ _ _ (der_30194 v h) (by intro d hd; cases hd)))
def cl_30648 : CNF.NClause := [(27,true),(78,true),(22,false),(6,true),(15,false)]
theorem der_30648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30648 :=
  CNF.rup_sound cl_30648 [cl_24610,cl_30197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24610 v h) (hints_cons _ _ _ (der_30197 v h) (by intro d hd; cases hd)))
def cl_30649 : CNF.NClause := [(78,true),(27,true),(6,true),(15,false),(4,false)]
theorem der_30649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30649 :=
  CNF.rup_sound cl_30649 [cl_24611,cl_30648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24611 v h) (hints_cons _ _ _ (der_30648 v h) (by intro d hd; cases hd)))
def cl_30650 : CNF.NClause := [(7,true),(19,true),(71,true),(26,false),(20,false)]
theorem der_30650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30650 :=
  CNF.rup_sound cl_30650 [cl_24612,cl_30332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24612 v h) (hints_cons _ _ _ (der_30332 v h) (by intro d hd; cases hd)))
def cl_30651 : CNF.NClause := [(16,false),(2,true),(28,false),(84,true),(24,false)]
theorem der_30651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30651 :=
  CNF.rup_sound cl_30651 [cl_24613,cl_30643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24613 v h) (hints_cons _ _ _ (der_30643 v h) (by intro d hd; cases hd)))
def cl_30652 : CNF.NClause := [(84,true),(13,true),(24,false),(28,false),(16,true)]
theorem der_30652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30652 :=
  CNF.rup_sound cl_30652 [cl_24614,cl_30362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24614 v h) (hints_cons _ _ _ (der_30362 v h) (by intro d hd; cases hd)))
def cl_30653 : CNF.NClause := [(28,false),(2,true),(5,false),(84,true),(16,false)]
theorem der_30653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30653 :=
  CNF.rup_sound cl_30653 [cl_24615,cl_30651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24615 v h) (hints_cons _ _ _ (der_30651 v h) (by intro d hd; cases hd)))
def cl_30654 : CNF.NClause := [(13,true),(28,false),(16,true),(5,false),(84,true)]
theorem der_30654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30654 :=
  CNF.rup_sound cl_30654 [cl_24616,cl_30652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24616 v h) (hints_cons _ _ _ (der_30652 v h) (by intro d hd; cases hd)))
def cl_30655 : CNF.NClause := [(16,false),(24,false),(5,false),(84,true),(2,true)]
theorem der_30655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30655 :=
  CNF.rup_sound cl_30655 [cl_24617,cl_30653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24617 v h) (hints_cons _ _ _ (der_30653 v h) (by intro d hd; cases hd)))
def cl_30656 : CNF.NClause := [(84,true),(28,true),(24,false),(5,false),(2,true)]
theorem der_30656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30656 :=
  CNF.rup_sound cl_30656 [cl_24618,cl_30655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24618 v h) (hints_cons _ _ _ (der_30655 v h) (by intro d hd; cases hd)))
def cl_30657 : CNF.NClause := [(84,true),(28,true),(24,true),(5,false),(16,false)]
theorem der_30657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30657 :=
  CNF.rup_sound cl_30657 [cl_24619,cl_30631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24619 v h) (hints_cons _ _ _ (der_30631 v h) (by intro d hd; cases hd)))
def cl_30658 : CNF.NClause := [(78,true),(15,false),(27,false),(22,false),(6,false)]
theorem der_30658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30658 :=
  CNF.rup_sound cl_30658 [cl_24620,cl_30566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24620 v h) (hints_cons _ _ _ (der_30566 v h) (by intro d hd; cases hd)))
def cl_30659 : CNF.NClause := [(78,true),(27,false),(15,true),(22,false),(6,false)]
theorem der_30659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30659 :=
  CNF.rup_sound cl_30659 [cl_24621,cl_30633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24621 v h) (hints_cons _ _ _ (der_30633 v h) (by intro d hd; cases hd)))
def cl_30660 : CNF.NClause := [(78,true),(4,true),(22,true),(15,false),(27,false)]
theorem der_30660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30660 :=
  CNF.rup_sound cl_30660 [cl_24622,cl_30194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24622 v h) (hints_cons _ _ _ (der_30194 v h) (by intro d hd; cases hd)))
def cl_30661 : CNF.NClause := [(78,true),(27,false),(15,true),(4,true),(6,false)]
theorem der_30661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30661 :=
  CNF.rup_sound cl_30661 [cl_24623,cl_30659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24623 v h) (hints_cons _ _ _ (der_30659 v h) (by intro d hd; cases hd)))
def cl_30662 : CNF.NClause := [(6,false),(78,true),(15,false),(27,true),(22,false)]
theorem der_30662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30662 :=
  CNF.rup_sound cl_30662 [cl_24624,cl_30636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24624 v h) (hints_cons _ _ _ (der_30636 v h) (by intro d hd; cases hd)))
def cl_30663 : CNF.NClause := [(78,true),(13,true),(15,true),(22,false),(6,false)]
theorem der_30663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30663 :=
  CNF.rup_sound cl_30663 [cl_24625,cl_30659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24625 v h) (hints_cons _ _ _ (der_30659 v h) (by intro d hd; cases hd)))
def cl_30664 : CNF.NClause := [(71,true),(1,false),(26,false),(19,false),(7,true)]
theorem der_30664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30664 :=
  CNF.rup_sound cl_30664 [cl_24626,cl_23598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24626 v h) (hints_cons _ _ _ (der_23598 v h) (by intro d hd; cases hd)))
def cl_30665 : CNF.NClause := [(71,true),(26,false),(1,false),(13,true),(7,true)]
theorem der_30665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30665 :=
  CNF.rup_sound cl_30665 [cl_24627,cl_30664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24627 v h) (hints_cons _ _ _ (der_30664 v h) (by intro d hd; cases hd)))
def cl_30666 : CNF.NClause := [(71,true),(7,true),(1,false),(20,false),(19,false)]
theorem der_30666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30666 :=
  CNF.rup_sound cl_30666 [cl_24628,cl_23599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24628 v h) (hints_cons _ _ _ (der_23599 v h) (by intro d hd; cases hd)))
def cl_30667 : CNF.NClause := [(13,true),(71,true),(26,false),(19,false),(7,false)]
theorem der_30667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30667 :=
  CNF.rup_sound cl_30667 [cl_24629,cl_30306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24629 v h) (hints_cons _ _ _ (der_30306 v h) (by intro d hd; cases hd)))
def cl_30669 : CNF.NClause := [(71,true),(20,false),(19,false),(1,false),(7,false)]
theorem der_30669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30669 :=
  CNF.rup_sound cl_30669 [cl_24631,cl_30008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24631 v h) (hints_cons _ _ _ (der_30008 v h) (by intro d hd; cases hd)))
def cl_30670 : CNF.NClause := [(7,false),(71,true),(20,false),(1,false),(19,true)]
theorem der_30670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30670 :=
  CNF.rup_sound cl_30670 [cl_24632,cl_30265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24632 v h) (hints_cons _ _ _ (der_30265 v h) (by intro d hd; cases hd)))
def cl_30671 : CNF.NClause := [(71,true),(7,false),(20,true),(19,true),(1,false)]
theorem der_30671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30671 :=
  CNF.rup_sound cl_30671 [cl_24634,cl_30283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24634 v h) (hints_cons _ _ _ (der_30283 v h) (by intro d hd; cases hd)))
def cl_30673 : CNF.NClause := [(9,true),(26,false),(3,false),(75,true),(16,false)]
theorem der_30673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30673 :=
  CNF.rup_sound cl_30673 [cl_24636,cl_30558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24636 v h) (hints_cons _ _ _ (der_30558 v h) (by intro d hd; cases hd)))
def cl_30674 : CNF.NClause := [(75,true),(9,true),(22,true),(3,false),(16,false)]
theorem der_30674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30674 :=
  CNF.rup_sound cl_30674 [cl_24638,cl_30673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24638 v h) (hints_cons _ _ _ (der_30673 v h) (by intro d hd; cases hd)))
def cl_30675 : CNF.NClause := [(10,false),(26,true),(16,true),(3,false),(75,true)]
theorem der_30675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30675 :=
  CNF.rup_sound cl_30675 [cl_24639,cl_23568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24639 v h) (hints_cons _ _ _ (der_23568 v h) (by intro d hd; cases hd)))
def cl_30676 : CNF.NClause := [(69,true),(20,false),(27,false),(18,false),(2,false)]
theorem der_30676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30676 :=
  CNF.rup_sound cl_30676 [cl_24641,cl_24371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24641 v h) (hints_cons _ _ _ (der_24371 v h) (by intro d hd; cases hd)))
def cl_30677 : CNF.NClause := [(69,true),(11,true),(20,false),(27,false),(18,true)]
theorem der_30677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30677 :=
  CNF.rup_sound cl_30677 [cl_24643,cl_30452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24643 v h) (hints_cons _ _ _ (der_30452 v h) (by intro d hd; cases hd)))
def cl_30678 : CNF.NClause := [(69,true),(20,true),(27,false),(11,false),(18,false)]
theorem der_30678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30678 :=
  CNF.rup_sound cl_30678 [cl_24644,cl_30281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24644 v h) (hints_cons _ _ _ (der_30281 v h) (by intro d hd; cases hd)))
def cl_30679 : CNF.NClause := [(9,true),(27,false),(69,true),(11,true),(18,false)]
theorem der_30679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30679 :=
  CNF.rup_sound cl_30679 [cl_24645,cl_24388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24645 v h) (hints_cons _ _ _ (der_24388 v h) (by intro d hd; cases hd)))
def cl_30680 : CNF.NClause := [(27,false),(11,false),(69,true),(18,true),(20,true)]
theorem der_30680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30680 :=
  CNF.rup_sound cl_30680 [cl_24646,cl_23583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24646 v h) (hints_cons _ _ _ (der_23583 v h) (by intro d hd; cases hd)))
def cl_30681 : CNF.NClause := [(69,true),(18,false),(20,false),(11,false),(27,true)]
theorem der_30681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30681 :=
  CNF.rup_sound cl_30681 [cl_24648,cl_30339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24648 v h) (hints_cons _ _ _ (der_30339 v h) (by intro d hd; cases hd)))
def cl_30682 : CNF.NClause := [(69,true),(9,true),(27,true),(18,false),(20,false)]
theorem der_30682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30682 :=
  CNF.rup_sound cl_30682 [cl_24649,cl_30681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24649 v h) (hints_cons _ _ _ (der_30681 v h) (by intro d hd; cases hd)))
def cl_30683 : CNF.NClause := [(69,true),(2,false),(20,false),(11,false),(18,true)]
theorem der_30683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30683 :=
  CNF.rup_sound cl_30683 [cl_24650,cl_30027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24650 v h) (hints_cons _ _ _ (der_30027 v h) (by intro d hd; cases hd)))
def cl_30684 : CNF.NClause := [(69,true),(11,true),(2,false),(20,false),(18,true)]
theorem der_30684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30684 :=
  CNF.rup_sound cl_30684 [cl_24651,cl_30677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24651 v h) (hints_cons _ _ _ (der_30677 v h) (by intro d hd; cases hd)))
def cl_30685 : CNF.NClause := [(69,true),(9,true),(27,true),(11,false),(18,false)]
theorem der_30685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30685 :=
  CNF.rup_sound cl_30685 [cl_24652,cl_30681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24652 v h) (hints_cons _ _ _ (der_30681 v h) (by intro d hd; cases hd)))
def cl_30686 : CNF.NClause := [(69,true),(20,true),(11,true),(18,false),(2,false)]
theorem der_30686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30686 :=
  CNF.rup_sound cl_30686 [cl_24653,cl_30443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24653 v h) (hints_cons _ _ _ (der_30443 v h) (by intro d hd; cases hd)))
def cl_30687 : CNF.NClause := [(11,false),(20,true),(69,true),(18,true),(2,false)]
theorem der_30687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30687 :=
  CNF.rup_sound cl_30687 [cl_24654,cl_30680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24654 v h) (hints_cons _ _ _ (der_30680 v h) (by intro d hd; cases hd)))
def cl_30688 : CNF.NClause := [(23,true),(81,true),(12,true),(15,false),(28,false)]
theorem der_30688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30688 :=
  CNF.rup_sound cl_30688 [cl_24655,cl_30351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24655 v h) (hints_cons _ _ _ (der_30351 v h) (by intro d hd; cases hd)))
def cl_30689 : CNF.NClause := [(28,true),(81,true),(9,true),(15,false),(1,false)]
theorem der_30689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30689 :=
  CNF.rup_sound cl_30689 [cl_24656,cl_30346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24656 v h) (hints_cons _ _ _ (der_30346 v h) (by intro d hd; cases hd)))
def cl_30690 : CNF.NClause := [(1,false),(15,false),(12,true),(23,false),(81,true)]
theorem der_30690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30690 :=
  CNF.rup_sound cl_30690 [cl_24658,cl_30355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24658 v h) (hints_cons _ _ _ (der_30355 v h) (by intro d hd; cases hd)))
def cl_30691 : CNF.NClause := [(1,false),(15,false),(23,false),(81,true),(12,false)]
theorem der_30691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30691 :=
  CNF.rup_sound cl_30691 [cl_24659,cl_30353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24659 v h) (hints_cons _ _ _ (der_30353 v h) (by intro d hd; cases hd)))
def cl_30692 : CNF.NClause := [(69,true),(9,true),(18,false),(11,false),(2,true)]
theorem der_30692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30692 :=
  CNF.rup_sound cl_30692 [cl_24660,cl_30284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24660 v h) (hints_cons _ _ _ (der_30284 v h) (by intro d hd; cases hd)))
def cl_30693 : CNF.NClause := [(9,true),(10,false),(3,false),(75,true),(22,false)]
theorem der_30693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30693 :=
  CNF.rup_sound cl_30693 [cl_24661,cl_23572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24661 v h) (hints_cons _ _ _ (der_23572 v h) (by intro d hd; cases hd)))
def cl_30694 : CNF.NClause := [(69,true),(18,true),(11,false),(27,false),(2,true)]
theorem der_30694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30694 :=
  CNF.rup_sound cl_30694 [cl_24662,cl_30281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24662 v h) (hints_cons _ _ _ (der_30281 v h) (by intro d hd; cases hd)))
def cl_30695 : CNF.NClause := [(22,true),(10,false),(16,true),(26,false),(75,true)]
theorem der_30695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30695 :=
  CNF.rup_sound cl_30695 [cl_24663,cl_30499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24663 v h) (hints_cons _ _ _ (der_30499 v h) (by intro d hd; cases hd)))
def cl_30696 : CNF.NClause := [(85,true),(27,false),(12,true),(5,true),(21,false)]
theorem der_30696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30696 :=
  CNF.rup_sound cl_30696 [cl_24664,cl_30217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24664 v h) (hints_cons _ _ _ (der_30217 v h) (by intro d hd; cases hd)))
def cl_30697 : CNF.NClause := [(3,false),(12,false),(5,false),(19,false),(85,true)]
theorem der_30697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30697 :=
  CNF.rup_sound cl_30697 [cl_24666,cl_30221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24666 v h) (hints_cons _ _ _ (der_30221 v h) (by intro d hd; cases hd)))
def cl_30698 : CNF.NClause := [(12,true),(3,false),(5,false),(27,false),(85,true)]
theorem der_30698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30698 :=
  CNF.rup_sound cl_30698 [cl_24667,cl_24288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24667 v h) (hints_cons _ _ _ (der_24288 v h) (by intro d hd; cases hd)))
def cl_30699 : CNF.NClause := [(85,true),(27,true),(19,false),(3,false),(5,false)]
theorem der_30699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30699 :=
  CNF.rup_sound cl_30699 [cl_24668,cl_30697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24668 v h) (hints_cons _ _ _ (der_30697 v h) (by intro d hd; cases hd)))
def cl_30700 : CNF.NClause := [(14,true),(8,false),(15,false),(26,false),(79,true)]
theorem der_30700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30700 :=
  CNF.rup_sound cl_30700 [cl_24669,cl_29819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24669 v h) (hints_cons _ _ _ (der_29819 v h) (by intro d hd; cases hd)))
def cl_30701 : CNF.NClause := [(79,true),(21,false),(14,true),(15,false),(8,false)]
theorem der_30701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30701 :=
  CNF.rup_sound cl_30701 [cl_24670,cl_29817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24670 v h) (hints_cons _ _ _ (der_29817 v h) (by intro d hd; cases hd)))
def cl_30702 : CNF.NClause := [(79,true),(14,false),(21,false),(8,false),(15,false)]
theorem der_30702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30702 :=
  CNF.rup_sound cl_30702 [cl_24671,cl_30134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24671 v h) (hints_cons _ _ _ (der_30134 v h) (by intro d hd; cases hd)))
def cl_30703 : CNF.NClause := [(27,false),(19,true),(12,false),(85,true),(21,false)]
theorem der_30703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30703 :=
  CNF.rup_sound cl_30703 [cl_24672,cl_30486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24672 v h) (hints_cons _ _ _ (der_30486 v h) (by intro d hd; cases hd)))
def cl_30704 : CNF.NClause := [(85,true),(27,true),(5,false),(12,false),(3,false)]
theorem der_30704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30704 :=
  CNF.rup_sound cl_30704 [cl_24673,cl_30223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24673 v h) (hints_cons _ _ _ (der_30223 v h) (by intro d hd; cases hd)))
def cl_30705 : CNF.NClause := [(7,true),(10,false),(73,true),(4,false),(18,false)]
theorem der_30705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30705 :=
  CNF.rup_sound cl_30705 [cl_24674,cl_30548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24674 v h) (hints_cons _ _ _ (der_30548 v h) (by intro d hd; cases hd)))
def cl_30706 : CNF.NClause := [(4,true),(10,false),(28,true),(73,true),(21,false)]
theorem der_30706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30706 :=
  CNF.rup_sound cl_30706 [cl_24675,cl_29976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24675 v h) (hints_cons _ _ _ (der_29976 v h) (by intro d hd; cases hd)))
def cl_30708 : CNF.NClause := [(31,false),(88,false),(89,true),(92,true),(87,true)]
theorem der_30708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30708 :=
  CNF.rup_sound cl_30708 [cl_24683,cl_24681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24683 v h) (hints_cons _ _ _ (der_24681 v h) (by intro d hd; cases hd)))
def cl_30709 : CNF.NClause := [(31,false),(90,false),(88,false),(89,false),(87,false)]
theorem der_30709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30709 :=
  CNF.rup_sound cl_30709 [cl_24685,cl_23680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24685 v h) (hints_cons _ _ _ (der_23680 v h) (by intro d hd; cases hd)))
def cl_30711 : CNF.NClause := [(31,false),(88,false),(90,true),(92,true),(87,true)]
theorem der_30711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30711 :=
  CNF.rup_sound cl_30711 [cl_24688,cl_30708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24688 v h) (hints_cons _ _ _ (der_30708 v h) (by intro d hd; cases hd)))
def cl_30712 : CNF.NClause := [(31,false),(88,false),(89,false),(87,false),(92,false)]
theorem der_30712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30712 :=
  CNF.rup_sound cl_30712 [cl_24690,cl_24689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24690 v h) (hints_cons _ _ _ (der_24689 v h) (by intro d hd; cases hd)))
def cl_30714 : CNF.NClause := [(56,false),(65,false),(63,false),(62,false),(64,false)]
theorem der_30714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30714 :=
  CNF.rup_sound cl_30714 [cl_24694,cl_24693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24694 v h) (hints_cons _ _ _ (der_24693 v h) (by intro d hd; cases hd)))
def cl_30717 : CNF.NClause := [(56,false),(92,false),(63,false),(62,false),(64,false)]
theorem der_30717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30717 :=
  CNF.rup_sound cl_30717 [cl_24698,cl_24697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24698 v h) (hints_cons _ _ _ (der_24697 v h) (by intro d hd; cases hd)))
def cl_30718 : CNF.NClause := [(56,false),(63,false),(62,false),(64,false),(66,false)]
theorem der_30718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30718 :=
  CNF.rup_sound cl_30718 [cl_24699,cl_24697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24699 v h) (hints_cons _ _ _ (der_24697 v h) (by intro d hd; cases hd)))
def cl_30719 : CNF.NClause := [(56,false),(62,true),(64,true),(65,true),(63,true)]
theorem der_30719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30719 :=
  CNF.rup_sound cl_30719 [cl_24702,cl_24701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24702 v h) (hints_cons _ _ _ (der_24701 v h) (by intro d hd; cases hd)))
def cl_30720 : CNF.NClause := [(56,false),(92,true),(63,false),(62,false),(64,false)]
theorem der_30720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30720 :=
  CNF.rup_sound cl_30720 [cl_24703,cl_30714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24703 v h) (hints_cons _ _ _ (der_30714 v h) (by intro d hd; cases hd)))
def cl_30721 : CNF.NClause := [(56,false),(92,false),(63,false),(64,false),(66,false)]
theorem der_30721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30721 :=
  CNF.rup_sound cl_30721 [cl_24704,cl_30717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24704 v h) (hints_cons _ _ _ (der_30717 v h) (by intro d hd; cases hd)))
def cl_30722 : CNF.NClause := [(56,false),(62,true),(92,false),(63,false),(64,false)]
theorem der_30722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30722 :=
  CNF.rup_sound cl_30722 [cl_24705,cl_30721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24705 v h) (hints_cons _ _ _ (der_30721 v h) (by intro d hd; cases hd)))
def cl_30723 : CNF.NClause := [(56,false),(62,true),(63,false),(64,false),(66,false)]
theorem der_30723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30723 :=
  CNF.rup_sound cl_30723 [cl_24706,cl_30722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24706 v h) (hints_cons _ _ _ (der_30722 v h) (by intro d hd; cases hd)))
def cl_30724 : CNF.NClause := [(56,false),(66,true),(63,false),(64,false),(62,true)]
theorem der_30724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30724 :=
  CNF.rup_sound cl_30724 [cl_24707,cl_30722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24707 v h) (hints_cons _ _ _ (der_30722 v h) (by intro d hd; cases hd)))
def cl_30725 : CNF.NClause := [(57,false),(39,true),(52,false),(33,false),(110,true)]
theorem der_30725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30725 :=
  CNF.rup_sound cl_30725 [cl_24710,cl_24709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24710 v h) (hints_cons _ _ _ (der_24709 v h) (by intro d hd; cases hd)))
def cl_30726 : CNF.NClause := [(57,false),(46,false),(33,false),(52,true),(110,true)]
theorem der_30726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30726 :=
  CNF.rup_sound cl_30726 [cl_24712,cl_24711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24712 v h) (hints_cons _ _ _ (der_24711 v h) (by intro d hd; cases hd)))
def cl_30727 : CNF.NClause := [(57,false),(52,true),(45,true),(33,false),(110,true)]
theorem der_30727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30727 :=
  CNF.rup_sound cl_30727 [cl_24714,cl_30726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24714 v h) (hints_cons _ _ _ (der_30726 v h) (by intro d hd; cases hd)))
def cl_30729 : CNF.NClause := [(45,false),(39,true),(52,false),(33,false),(110,true)]
theorem der_30729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30729 :=
  CNF.rup_sound cl_30729 [cl_24717,cl_24715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24717 v h) (hints_cons _ _ _ (der_24715 v h) (by intro d hd; cases hd)))
def cl_30730 : CNF.NClause := [(52,false),(57,true),(39,true),(33,false),(110,true)]
theorem der_30730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30730 :=
  CNF.rup_sound cl_30730 [cl_24718,cl_30729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24718 v h) (hints_cons _ _ _ (der_30729 v h) (by intro d hd; cases hd)))
def cl_30731 : CNF.NClause := [(46,false),(33,false),(39,true),(57,true),(110,true)]
theorem der_30731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30731 :=
  CNF.rup_sound cl_30731 [cl_24720,cl_24719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24720 v h) (hints_cons _ _ _ (der_24719 v h) (by intro d hd; cases hd)))
def cl_30732 : CNF.NClause := [(45,false),(39,true),(33,false),(46,true),(110,true)]
theorem der_30732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30732 :=
  CNF.rup_sound cl_30732 [cl_24721,cl_30729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24721 v h) (hints_cons _ _ _ (der_30729 v h) (by intro d hd; cases hd)))
def cl_30733 : CNF.NClause := [(41,false),(32,false),(58,false),(55,false),(107,true)]
theorem der_30733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30733 :=
  CNF.rup_sound cl_30733 [cl_24724,cl_24722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24724 v h) (hints_cons _ _ _ (der_24722 v h) (by intro d hd; cases hd)))
def cl_30734 : CNF.NClause := [(32,false),(58,false),(55,false),(39,true),(107,true)]
theorem der_30734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30734 :=
  CNF.rup_sound cl_30734 [cl_24725,cl_30733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24725 v h) (hints_cons _ _ _ (der_30733 v h) (by intro d hd; cases hd)))
def cl_30735 : CNF.NClause := [(32,false),(48,false),(58,false),(39,true),(107,true)]
theorem der_30735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30735 :=
  CNF.rup_sound cl_30735 [cl_24727,cl_24726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24727 v h) (hints_cons _ _ _ (der_24726 v h) (by intro d hd; cases hd)))
def cl_30736 : CNF.NClause := [(41,false),(32,false),(58,false),(39,true),(107,true)]
theorem der_30736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30736 :=
  CNF.rup_sound cl_30736 [cl_24728,cl_30733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24728 v h) (hints_cons _ _ _ (der_30733 v h) (by intro d hd; cases hd)))
def cl_30737 : CNF.NClause := [(32,false),(58,false),(39,true),(41,true),(107,true)]
theorem der_30737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30737 :=
  CNF.rup_sound cl_30737 [cl_24729,cl_30735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24729 v h) (hints_cons _ _ _ (der_30735 v h) (by intro d hd; cases hd)))
def cl_30738 : CNF.NClause := [(32,false),(48,false),(55,false),(39,true),(107,true)]
theorem der_30738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30738 :=
  CNF.rup_sound cl_30738 [cl_24731,cl_24730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24731 v h) (hints_cons _ _ _ (der_24730 v h) (by intro d hd; cases hd)))
def cl_30739 : CNF.NClause := [(41,false),(32,false),(55,false),(39,true),(107,true)]
theorem der_30739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30739 :=
  CNF.rup_sound cl_30739 [cl_24732,cl_24730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24732 v h) (hints_cons _ _ _ (der_24730 v h) (by intro d hd; cases hd)))
def cl_30740 : CNF.NClause := [(32,false),(55,false),(39,true),(48,true),(107,true)]
theorem der_30740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30740 :=
  CNF.rup_sound cl_30740 [cl_24733,cl_30739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24733 v h) (hints_cons _ _ _ (der_30739 v h) (by intro d hd; cases hd)))
def cl_30741 : CNF.NClause := [(41,false),(32,false),(48,false),(39,true),(107,true)]
theorem der_30741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30741 :=
  CNF.rup_sound cl_30741 [cl_24734,cl_30739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24734 v h) (hints_cons _ _ _ (der_30739 v h) (by intro d hd; cases hd)))
def cl_30742 : CNF.NClause := [(32,false),(48,false),(39,true),(58,true),(107,true)]
theorem der_30742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30742 :=
  CNF.rup_sound cl_30742 [cl_24735,cl_30741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24735 v h) (hints_cons _ _ _ (der_30741 v h) (by intro d hd; cases hd)))
def cl_30743 : CNF.NClause := [(41,false),(32,false),(39,true),(48,true),(107,true)]
theorem der_30743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30743 :=
  CNF.rup_sound cl_30743 [cl_24736,cl_30739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24736 v h) (hints_cons _ _ _ (der_30739 v h) (by intro d hd; cases hd)))
def cl_30744 : CNF.NClause := [(35,false),(51,false),(60,false),(43,false),(99,true)]
theorem der_30744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30744 :=
  CNF.rup_sound cl_30744 [cl_24739,cl_24737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24739 v h) (hints_cons _ _ _ (der_24737 v h) (by intro d hd; cases hd)))
def cl_30745 : CNF.NClause := [(35,false),(51,false),(60,false),(39,true),(99,true)]
theorem der_30745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30745 :=
  CNF.rup_sound cl_30745 [cl_24740,cl_24738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24740 v h) (hints_cons _ _ _ (der_24738 v h) (by intro d hd; cases hd)))
def cl_30746 : CNF.NClause := [(35,false),(60,false),(47,false),(39,true),(99,true)]
theorem der_30746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30746 :=
  CNF.rup_sound cl_30746 [cl_24742,cl_24738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24742 v h) (hints_cons _ _ _ (der_24738 v h) (by intro d hd; cases hd)))
def cl_30747 : CNF.NClause := [(35,false),(60,false),(43,false),(39,true),(99,true)]
theorem der_30747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30747 :=
  CNF.rup_sound cl_30747 [cl_24743,cl_24741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24743 v h) (hints_cons _ _ _ (der_24741 v h) (by intro d hd; cases hd)))
def cl_30748 : CNF.NClause := [(35,false),(60,false),(39,true),(51,true),(99,true)]
theorem der_30748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30748 :=
  CNF.rup_sound cl_30748 [cl_24744,cl_30747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24744 v h) (hints_cons _ _ _ (der_30747 v h) (by intro d hd; cases hd)))
def cl_30749 : CNF.NClause := [(35,false),(51,false),(47,false),(39,true),(99,true)]
theorem der_30749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30749 :=
  CNF.rup_sound cl_30749 [cl_24746,cl_30746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24746 v h) (hints_cons _ _ _ (der_30746 v h) (by intro d hd; cases hd)))
def cl_30750 : CNF.NClause := [(35,false),(51,false),(43,false),(47,true),(99,true)]
theorem der_30750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30750 :=
  CNF.rup_sound cl_30750 [cl_24747,cl_30744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24747 v h) (hints_cons _ _ _ (der_30744 v h) (by intro d hd; cases hd)))
def cl_30751 : CNF.NClause := [(35,false),(51,false),(39,true),(43,true),(99,true)]
theorem der_30751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30751 :=
  CNF.rup_sound cl_30751 [cl_24748,cl_30749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24748 v h) (hints_cons _ _ _ (der_30749 v h) (by intro d hd; cases hd)))
def cl_30752 : CNF.NClause := [(35,false),(39,true),(47,false),(43,false),(99,true)]
theorem der_30752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30752 :=
  CNF.rup_sound cl_30752 [cl_24749,cl_30747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24749 v h) (hints_cons _ _ _ (der_30747 v h) (by intro d hd; cases hd)))
def cl_30753 : CNF.NClause := [(35,false),(47,false),(39,true),(43,true),(99,true)]
theorem der_30753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30753 :=
  CNF.rup_sound cl_30753 [cl_24750,cl_30746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24750 v h) (hints_cons _ _ _ (der_30746 v h) (by intro d hd; cases hd)))
def cl_30754 : CNF.NClause := [(35,false),(39,true),(47,true),(43,false),(99,true)]
theorem der_30754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30754 :=
  CNF.rup_sound cl_30754 [cl_24751,cl_30750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24751 v h) (hints_cons _ _ _ (der_30750 v h) (by intro d hd; cases hd)))
def cl_30755 : CNF.NClause := [(34,false),(44,false),(49,true),(54,true),(96,true)]
theorem der_30755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30755 :=
  CNF.rup_sound cl_30755 [cl_24755,cl_23809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24755 v h) (hints_cons _ _ _ (der_23809 v h) (by intro d hd; cases hd)))
def cl_30757 : CNF.NClause := [(36,false),(37,false),(39,true),(61,true),(113,true)]
theorem der_30757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30757 :=
  CNF.rup_sound cl_30757 [cl_24757,cl_23671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24757 v h) (hints_cons _ _ _ (der_23671 v h) (by intro d hd; cases hd)))
def cl_30758 : CNF.NClause := [(59,false),(50,false),(42,false),(31,true),(121,true)]
theorem der_30758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30758 :=
  CNF.rup_sound cl_30758 [cl_24758,cl_23742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24758 v h) (hints_cons _ _ _ (der_23742 v h) (by intro d hd; cases hd)))
def cl_30759 : CNF.NClause := [(60,false),(54,false),(37,true),(33,false),(105,true)]
theorem der_30759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30759 :=
  CNF.rup_sound cl_30759 [cl_24763,cl_24762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24763 v h) (hints_cons _ _ _ (der_24762 v h) (by intro d hd; cases hd)))
def cl_30760 : CNF.NClause := [(50,false),(60,false),(37,true),(33,false),(105,true)]
theorem der_30760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30760 :=
  CNF.rup_sound cl_30760 [cl_24765,cl_24764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24765 v h) (hints_cons _ _ _ (der_24764 v h) (by intro d hd; cases hd)))
def cl_30761 : CNF.NClause := [(41,false),(60,false),(33,false),(37,true),(105,true)]
theorem der_30761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30761 :=
  CNF.rup_sound cl_30761 [cl_24766,cl_30760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24766 v h) (hints_cons _ _ _ (der_30760 v h) (by intro d hd; cases hd)))
def cl_30762 : CNF.NClause := [(60,false),(41,true),(37,true),(33,false),(105,true)]
theorem der_30762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30762 :=
  CNF.rup_sound cl_30762 [cl_24767,cl_30759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24767 v h) (hints_cons _ _ _ (der_30759 v h) (by intro d hd; cases hd)))
def cl_30763 : CNF.NClause := [(41,false),(50,false),(33,false),(54,false),(105,true)]
theorem der_30763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30763 :=
  CNF.rup_sound cl_30763 [cl_24768,cl_24760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24768 v h) (hints_cons _ _ _ (der_24760 v h) (by intro d hd; cases hd)))
def cl_30764 : CNF.NClause := [(50,false),(54,false),(37,true),(33,false),(105,true)]
theorem der_30764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30764 :=
  CNF.rup_sound cl_30764 [cl_24769,cl_30763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24769 v h) (hints_cons _ _ _ (der_30763 v h) (by intro d hd; cases hd)))
def cl_30765 : CNF.NClause := [(41,false),(54,false),(33,false),(37,true),(105,true)]
theorem der_30765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30765 :=
  CNF.rup_sound cl_30765 [cl_24770,cl_30763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24770 v h) (hints_cons _ _ _ (der_30763 v h) (by intro d hd; cases hd)))
def cl_30766 : CNF.NClause := [(54,false),(50,true),(37,true),(33,false),(105,true)]
theorem der_30766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30766 :=
  CNF.rup_sound cl_30766 [cl_24771,cl_30759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24771 v h) (hints_cons _ _ _ (der_30759 v h) (by intro d hd; cases hd)))
def cl_30767 : CNF.NClause := [(41,false),(50,false),(33,false),(37,true),(105,true)]
theorem der_30767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30767 :=
  CNF.rup_sound cl_30767 [cl_24772,cl_30763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24772 v h) (hints_cons _ _ _ (der_30763 v h) (by intro d hd; cases hd)))
def cl_30768 : CNF.NClause := [(50,false),(37,true),(33,false),(54,true),(105,true)]
theorem der_30768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30768 :=
  CNF.rup_sound cl_30768 [cl_24773,cl_30760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24773 v h) (hints_cons _ _ _ (der_30760 v h) (by intro d hd; cases hd)))
def cl_30769 : CNF.NClause := [(41,false),(37,true),(33,false),(60,true),(105,true)]
theorem der_30769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30769 :=
  CNF.rup_sound cl_30769 [cl_24774,cl_30765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24774 v h) (hints_cons _ _ _ (der_30765 v h) (by intro d hd; cases hd)))
def cl_30772 : CNF.NClause := [(32,false),(42,false),(56,false),(37,true),(97,true)]
theorem der_30772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30772 :=
  CNF.rup_sound cl_30772 [cl_24780,cl_24778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24780 v h) (hints_cons _ _ _ (der_24778 v h) (by intro d hd; cases hd)))
def cl_30774 : CNF.NClause := [(32,false),(52,false),(47,false),(37,true),(97,true)]
theorem der_30774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30774 :=
  CNF.rup_sound cl_30774 [cl_24783,cl_24782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24783 v h) (hints_cons _ _ _ (der_24782 v h) (by intro d hd; cases hd)))
def cl_30775 : CNF.NClause := [(32,false),(42,false),(52,false),(37,true),(97,true)]
theorem der_30775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30775 :=
  CNF.rup_sound cl_30775 [cl_24784,cl_24782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24784 v h) (hints_cons _ _ _ (der_24782 v h) (by intro d hd; cases hd)))
def cl_30776 : CNF.NClause := [(32,false),(52,false),(37,true),(42,true),(97,true)]
theorem der_30776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30776 :=
  CNF.rup_sound cl_30776 [cl_24785,cl_30774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24785 v h) (hints_cons _ _ _ (der_30774 v h) (by intro d hd; cases hd)))
def cl_30777 : CNF.NClause := [(32,false),(47,false),(37,true),(42,true),(97,true)]
theorem der_30777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30777 :=
  CNF.rup_sound cl_30777 [cl_24787,cl_30776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24787 v h) (hints_cons _ _ _ (der_30776 v h) (by intro d hd; cases hd)))
def cl_30778 : CNF.NClause := [(32,false),(42,false),(56,true),(52,true),(97,true)]
theorem der_30778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30778 :=
  CNF.rup_sound cl_30778 [cl_24788,cl_24786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24788 v h) (hints_cons _ _ _ (der_24786 v h) (by intro d hd; cases hd)))
def cl_30779 : CNF.NClause := [(35,false),(58,false),(44,false),(53,true),(109,true)]
theorem der_30779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30779 :=
  CNF.rup_sound cl_30779 [cl_24794,cl_24792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24794 v h) (hints_cons _ _ _ (der_24792 v h) (by intro d hd; cases hd)))
def cl_30780 : CNF.NClause := [(35,false),(58,false),(53,true),(46,true),(109,true)]
theorem der_30780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30780 :=
  CNF.rup_sound cl_30780 [cl_24795,cl_30119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24795 v h) (hints_cons _ _ _ (der_30119 v h) (by intro d hd; cases hd)))
def cl_30781 : CNF.NClause := [(35,false),(46,false),(53,false),(44,true),(109,true)]
theorem der_30781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30781 :=
  CNF.rup_sound cl_30781 [cl_24797,cl_24789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24797 v h) (hints_cons _ _ _ (der_24789 v h) (by intro d hd; cases hd)))
def cl_30782 : CNF.NClause := [(35,false),(44,false),(53,false),(37,true),(109,true)]
theorem der_30782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30782 :=
  CNF.rup_sound cl_30782 [cl_24798,cl_24796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24798 v h) (hints_cons _ _ _ (der_24796 v h) (by intro d hd; cases hd)))
def cl_30783 : CNF.NClause := [(35,false),(58,true),(37,true),(53,false),(109,true)]
theorem der_30783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30783 :=
  CNF.rup_sound cl_30783 [cl_24799,cl_30782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24799 v h) (hints_cons _ _ _ (der_30782 v h) (by intro d hd; cases hd)))
def cl_30784 : CNF.NClause := [(35,false),(46,false),(44,false),(53,true),(109,true)]
theorem der_30784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30784 :=
  CNF.rup_sound cl_30784 [cl_24800,cl_30779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24800 v h) (hints_cons _ _ _ (der_30779 v h) (by intro d hd; cases hd)))
def cl_30785 : CNF.NClause := [(35,false),(46,false),(37,true),(44,true),(109,true)]
theorem der_30785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30785 :=
  CNF.rup_sound cl_30785 [cl_24801,cl_24793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24801 v h) (hints_cons _ _ _ (der_24793 v h) (by intro d hd; cases hd)))
def cl_30786 : CNF.NClause := [(35,false),(44,false),(53,true),(58,true),(109,true)]
theorem der_30786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30786 :=
  CNF.rup_sound cl_30786 [cl_24802,cl_30784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24802 v h) (hints_cons _ _ _ (der_30784 v h) (by intro d hd; cases hd)))
def cl_30789 : CNF.NClause := [(59,false),(48,false),(34,false),(37,true),(101,true)]
theorem der_30789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30789 :=
  CNF.rup_sound cl_30789 [cl_24808,cl_24807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24808 v h) (hints_cons _ _ _ (der_24807 v h) (by intro d hd; cases hd)))
def cl_30790 : CNF.NClause := [(59,false),(45,false),(34,false),(37,true),(101,true)]
theorem der_30790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30790 :=
  CNF.rup_sound cl_30790 [cl_24809,cl_24807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24809 v h) (hints_cons _ _ _ (der_24807 v h) (by intro d hd; cases hd)))
def cl_30791 : CNF.NClause := [(59,false),(34,false),(37,true),(48,true),(101,true)]
theorem der_30791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30791 :=
  CNF.rup_sound cl_30791 [cl_24810,cl_30790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24810 v h) (hints_cons _ _ _ (der_30790 v h) (by intro d hd; cases hd)))
def cl_30792 : CNF.NClause := [(51,false),(48,false),(34,false),(37,true),(101,true)]
theorem der_30792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30792 :=
  CNF.rup_sound cl_30792 [cl_24812,cl_24811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24812 v h) (hints_cons _ _ _ (der_24811 v h) (by intro d hd; cases hd)))
def cl_30793 : CNF.NClause := [(51,false),(45,false),(34,false),(37,true),(101,true)]
theorem der_30793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30793 :=
  CNF.rup_sound cl_30793 [cl_24813,cl_24805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24813 v h) (hints_cons _ _ _ (der_24805 v h) (by intro d hd; cases hd)))
def cl_30794 : CNF.NClause := [(51,false),(34,false),(37,true),(48,true),(101,true)]
theorem der_30794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30794 :=
  CNF.rup_sound cl_30794 [cl_24814,cl_30793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24814 v h) (hints_cons _ _ _ (der_30793 v h) (by intro d hd; cases hd)))
def cl_30796 : CNF.NClause := [(48,false),(34,false),(45,true),(37,true),(101,true)]
theorem der_30796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30796 :=
  CNF.rup_sound cl_30796 [cl_24816,cl_30792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24816 v h) (hints_cons _ _ _ (der_30792 v h) (by intro d hd; cases hd)))
def cl_30797 : CNF.NClause := [(45,false),(34,false),(37,true),(59,true),(101,true)]
theorem der_30797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30797 :=
  CNF.rup_sound cl_30797 [cl_24817,cl_30793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24817 v h) (hints_cons _ _ _ (der_30793 v h) (by intro d hd; cases hd)))
def cl_30798 : CNF.NClause := [(61,false),(39,false),(36,false),(40,false),(113,true)]
theorem der_30798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30798 :=
  CNF.rup_sound cl_30798 [cl_24819,cl_24818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24819 v h) (hints_cons _ _ _ (der_24818 v h) (by intro d hd; cases hd)))
def cl_30800 : CNF.NClause := [(61,false),(36,false),(40,false),(37,true),(113,true)]
theorem der_30800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30800 :=
  CNF.rup_sound cl_30800 [cl_24821,cl_30798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24821 v h) (hints_cons _ _ _ (der_30798 v h) (by intro d hd; cases hd)))
def cl_30801 : CNF.NClause := [(61,false),(39,false),(36,false),(38,false),(113,true)]
theorem der_30801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30801 :=
  CNF.rup_sound cl_30801 [cl_24822,cl_24818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24822 v h) (hints_cons _ _ _ (der_24818 v h) (by intro d hd; cases hd)))
def cl_30802 : CNF.NClause := [(61,false),(39,false),(36,false),(38,true),(113,true)]
theorem der_30802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30802 :=
  CNF.rup_sound cl_30802 [cl_24823,cl_23670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24823 v h) (hints_cons _ _ _ (der_23670 v h) (by intro d hd; cases hd)))
def cl_30803 : CNF.NClause := [(61,false),(36,false),(38,false),(39,true),(113,true)]
theorem der_30803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30803 :=
  CNF.rup_sound cl_30803 [cl_24824,cl_30045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24824 v h) (hints_cons _ _ _ (der_30045 v h) (by intro d hd; cases hd)))
def cl_30805 : CNF.NClause := [(39,false),(36,false),(40,false),(38,false),(113,true)]
theorem der_30805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30805 :=
  CNF.rup_sound cl_30805 [cl_24826,cl_23715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24826 v h) (hints_cons _ _ _ (der_23715 v h) (by intro d hd; cases hd)))
def cl_30806 : CNF.NClause := [(39,false),(36,false),(40,false),(38,true),(113,true)]
theorem der_30806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30806 :=
  CNF.rup_sound cl_30806 [cl_24827,cl_30802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24827 v h) (hints_cons _ _ _ (der_30802 v h) (by intro d hd; cases hd)))
def cl_30807 : CNF.NClause := [(36,false),(40,false),(38,false),(39,true),(113,true)]
theorem der_30807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30807 :=
  CNF.rup_sound cl_30807 [cl_24828,cl_30803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24828 v h) (hints_cons _ _ _ (der_30803 v h) (by intro d hd; cases hd)))
def cl_30808 : CNF.NClause := [(36,false),(40,false),(39,true),(61,true),(113,true)]
theorem der_30808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30808 :=
  CNF.rup_sound cl_30808 [cl_24829,cl_30807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24829 v h) (hints_cons _ _ _ (der_30807 v h) (by intro d hd; cases hd)))
def cl_30809 : CNF.NClause := [(39,false),(36,false),(38,false),(37,true),(113,true)]
theorem der_30809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30809 :=
  CNF.rup_sound cl_30809 [cl_24830,cl_30801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24830 v h) (hints_cons _ _ _ (der_30801 v h) (by intro d hd; cases hd)))
def cl_30810 : CNF.NClause := [(36,false),(38,false),(39,true),(40,true),(113,true)]
theorem der_30810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30810 :=
  CNF.rup_sound cl_30810 [cl_24832,cl_30803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24832 v h) (hints_cons _ _ _ (der_30803 v h) (by intro d hd; cases hd)))
def cl_30811 : CNF.NClause := [(57,false),(31,true),(49,true),(43,false),(122,true)]
theorem der_30811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30811 :=
  CNF.rup_sound cl_30811 [cl_24836,cl_24833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24836 v h) (hints_cons _ _ _ (der_24833 v h) (by intro d hd; cases hd)))
def cl_30812 : CNF.NClause := [(61,false),(39,false),(40,false),(38,false),(113,true)]
theorem der_30812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30812 :=
  CNF.rup_sound cl_30812 [cl_24842,cl_24841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24842 v h) (hints_cons _ _ _ (der_24841 v h) (by intro d hd; cases hd)))
def cl_30815 : CNF.NClause := [(61,false),(37,false),(40,false),(38,false),(113,true)]
theorem der_30815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30815 :=
  CNF.rup_sound cl_30815 [cl_24845,cl_30812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24845 v h) (hints_cons _ _ _ (der_30812 v h) (by intro d hd; cases hd)))
def cl_30817 : CNF.NClause := [(61,false),(37,false),(40,false),(36,true),(113,true)]
theorem der_30817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30817 :=
  CNF.rup_sound cl_30817 [cl_24847,cl_30815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24847 v h) (hints_cons _ _ _ (der_30815 v h) (by intro d hd; cases hd)))
def cl_30820 : CNF.NClause := [(61,false),(39,false),(38,false),(36,true),(113,true)]
theorem der_30820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30820 :=
  CNF.rup_sound cl_30820 [cl_24850,cl_30812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24850 v h) (hints_cons _ _ _ (der_30812 v h) (by intro d hd; cases hd)))
def cl_30821 : CNF.NClause := [(61,false),(39,false),(37,false),(38,true),(113,true)]
theorem der_30821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30821 :=
  CNF.rup_sound cl_30821 [cl_24851,cl_23670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24851 v h) (hints_cons _ _ _ (der_23670 v h) (by intro d hd; cases hd)))
def cl_30822 : CNF.NClause := [(61,false),(39,false),(38,true),(37,true),(113,true)]
theorem der_30822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30822 :=
  CNF.rup_sound cl_30822 [cl_24852,cl_30802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24852 v h) (hints_cons _ _ _ (der_30802 v h) (by intro d hd; cases hd)))
def cl_30826 : CNF.NClause := [(39,false),(37,false),(40,false),(38,false),(113,true)]
theorem der_30826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30826 :=
  CNF.rup_sound cl_30826 [cl_24856,cl_23715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24856 v h) (hints_cons _ _ _ (der_23715 v h) (by intro d hd; cases hd)))
def cl_30827 : CNF.NClause := [(39,false),(40,false),(38,false),(61,true),(113,true)]
theorem der_30827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30827 :=
  CNF.rup_sound cl_30827 [cl_24857,cl_30805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24857 v h) (hints_cons _ _ _ (der_30805 v h) (by intro d hd; cases hd)))
def cl_30828 : CNF.NClause := [(39,false),(37,false),(40,false),(36,true),(113,true)]
theorem der_30828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30828 :=
  CNF.rup_sound cl_30828 [cl_24858,cl_30826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24858 v h) (hints_cons _ _ _ (der_30826 v h) (by intro d hd; cases hd)))
def cl_30829 : CNF.NClause := [(39,false),(40,false),(38,true),(37,true),(113,true)]
theorem der_30829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30829 :=
  CNF.rup_sound cl_30829 [cl_24859,cl_30806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24859 v h) (hints_cons _ _ _ (der_30806 v h) (by intro d hd; cases hd)))
def cl_30830 : CNF.NClause := [(37,false),(40,false),(38,false),(39,true),(113,true)]
theorem der_30830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30830 :=
  CNF.rup_sound cl_30830 [cl_24860,cl_30815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24860 v h) (hints_cons _ _ _ (der_30815 v h) (by intro d hd; cases hd)))
def cl_30831 : CNF.NClause := [(40,false),(38,false),(39,true),(37,true),(113,true)]
theorem der_30831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30831 :=
  CNF.rup_sound cl_30831 [cl_24861,cl_30807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24861 v h) (hints_cons _ _ _ (der_30807 v h) (by intro d hd; cases hd)))
def cl_30832 : CNF.NClause := [(37,false),(40,false),(39,true),(61,true),(113,true)]
theorem der_30832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30832 :=
  CNF.rup_sound cl_30832 [cl_24862,cl_30830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24862 v h) (hints_cons _ _ _ (der_30830 v h) (by intro d hd; cases hd)))
def cl_30834 : CNF.NClause := [(39,false),(38,false),(40,true),(36,true),(113,true)]
theorem der_30834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30834 :=
  CNF.rup_sound cl_30834 [cl_24864,cl_30820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24864 v h) (hints_cons _ _ _ (der_30820 v h) (by intro d hd; cases hd)))
def cl_30835 : CNF.NClause := [(39,false),(37,false),(36,true),(61,true),(113,true)]
theorem der_30835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30835 :=
  CNF.rup_sound cl_30835 [cl_24865,cl_30828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24865 v h) (hints_cons _ _ _ (der_30828 v h) (by intro d hd; cases hd)))
def cl_30836 : CNF.NClause := [(37,false),(38,false),(39,true),(61,true),(113,true)]
theorem der_30836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30836 :=
  CNF.rup_sound cl_30836 [cl_24866,cl_30830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24866 v h) (hints_cons _ _ _ (der_30830 v h) (by intro d hd; cases hd)))
def cl_30837 : CNF.NClause := [(59,false),(55,false),(33,false),(44,true),(115,true)]
theorem der_30837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30837 :=
  CNF.rup_sound cl_30837 [cl_24869,cl_24867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24869 v h) (hints_cons _ _ _ (der_24867 v h) (by intro d hd; cases hd)))
def cl_30838 : CNF.NClause := [(59,false),(44,true),(47,false),(33,false),(115,true)]
theorem der_30838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30838 :=
  CNF.rup_sound cl_30838 [cl_24871,cl_30837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24871 v h) (hints_cons _ _ _ (der_30837 v h) (by intro d hd; cases hd)))
def cl_30839 : CNF.NClause := [(59,false),(44,true),(33,false),(36,true),(115,true)]
theorem der_30839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30839 :=
  CNF.rup_sound cl_30839 [cl_24873,cl_30838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24873 v h) (hints_cons _ _ _ (der_30838 v h) (by intro d hd; cases hd)))
def cl_30840 : CNF.NClause := [(55,false),(44,true),(47,false),(33,false),(115,true)]
theorem der_30840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30840 :=
  CNF.rup_sound cl_30840 [cl_24875,cl_30837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24875 v h) (hints_cons _ _ _ (der_30837 v h) (by intro d hd; cases hd)))
def cl_30841 : CNF.NClause := [(55,false),(36,true),(44,false),(33,false),(115,true)]
theorem der_30841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30841 :=
  CNF.rup_sound cl_30841 [cl_24876,cl_24874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24876 v h) (hints_cons _ _ _ (der_24874 v h) (by intro d hd; cases hd)))
def cl_30842 : CNF.NClause := [(55,false),(47,true),(33,false),(36,true),(115,true)]
theorem der_30842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30842 :=
  CNF.rup_sound cl_30842 [cl_24877,cl_30841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24877 v h) (hints_cons _ _ _ (der_30841 v h) (by intro d hd; cases hd)))
def cl_30843 : CNF.NClause := [(47,false),(44,false),(36,true),(33,false),(115,true)]
theorem der_30843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30843 :=
  CNF.rup_sound cl_30843 [cl_24878,cl_30841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24878 v h) (hints_cons _ _ _ (der_30841 v h) (by intro d hd; cases hd)))
def cl_30844 : CNF.NClause := [(47,false),(55,true),(44,true),(33,false),(115,true)]
theorem der_30844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30844 :=
  CNF.rup_sound cl_30844 [cl_24879,cl_30838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24879 v h) (hints_cons _ _ _ (der_30838 v h) (by intro d hd; cases hd)))
def cl_30845 : CNF.NClause := [(44,false),(55,true),(47,true),(33,false),(115,true)]
theorem der_30845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30845 :=
  CNF.rup_sound cl_30845 [cl_24880,cl_24872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24880 v h) (hints_cons _ _ _ (der_24872 v h) (by intro d hd; cases hd)))
def cl_30846 : CNF.NClause := [(32,false),(60,false),(45,false),(53,true),(117,true)]
theorem der_30846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30846 :=
  CNF.rup_sound cl_30846 [cl_24886,cl_24884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24886 v h) (hints_cons _ _ _ (der_24884 v h) (by intro d hd; cases hd)))
def cl_30847 : CNF.NClause := [(32,false),(60,false),(45,true),(36,true),(117,true)]
theorem der_30847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30847 :=
  CNF.rup_sound cl_30847 [cl_24887,cl_24885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24887 v h) (hints_cons _ _ _ (der_24885 v h) (by intro d hd; cases hd)))
def cl_30848 : CNF.NClause := [(32,false),(117,true),(49,false),(36,true),(53,false)]
theorem der_30848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30848 :=
  CNF.rup_sound cl_30848 [cl_24889,cl_24888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24889 v h) (hints_cons _ _ _ (der_24888 v h) (by intro d hd; cases hd)))
def cl_30849 : CNF.NClause := [(32,false),(45,false),(53,false),(49,true),(117,true)]
theorem der_30849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30849 :=
  CNF.rup_sound cl_30849 [cl_24890,cl_24882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24890 v h) (hints_cons _ _ _ (der_24882 v h) (by intro d hd; cases hd)))
def cl_30850 : CNF.NClause := [(32,false),(117,true),(45,true),(36,true),(53,false)]
theorem der_30850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30850 :=
  CNF.rup_sound cl_30850 [cl_24891,cl_30848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24891 v h) (hints_cons _ _ _ (der_30848 v h) (by intro d hd; cases hd)))
def cl_30851 : CNF.NClause := [(32,false),(45,false),(49,false),(53,true),(117,true)]
theorem der_30851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30851 :=
  CNF.rup_sound cl_30851 [cl_24892,cl_24884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24892 v h) (hints_cons _ _ _ (der_24884 v h) (by intro d hd; cases hd)))
def cl_30852 : CNF.NClause := [(32,false),(49,false),(45,true),(36,true),(117,true)]
theorem der_30852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30852 :=
  CNF.rup_sound cl_30852 [cl_24893,cl_24885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24893 v h) (hints_cons _ _ _ (der_24885 v h) (by intro d hd; cases hd)))
def cl_30853 : CNF.NClause := [(32,false),(45,false),(53,true),(60,true),(117,true)]
theorem der_30853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30853 :=
  CNF.rup_sound cl_30853 [cl_24894,cl_30851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24894 v h) (hints_cons _ _ _ (der_30851 v h) (by intro d hd; cases hd)))
def cl_30854 : CNF.NClause := [(35,false),(57,false),(42,false),(54,false),(114,true)]
theorem der_30854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30854 :=
  CNF.rup_sound cl_30854 [cl_24897,cl_24895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24897 v h) (hints_cons _ _ _ (der_24895 v h) (by intro d hd; cases hd)))
def cl_30855 : CNF.NClause := [(35,false),(57,false),(54,false),(36,true),(114,true)]
theorem der_30855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30855 :=
  CNF.rup_sound cl_30855 [cl_24898,cl_30854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24898 v h) (hints_cons _ _ _ (der_30854 v h) (by intro d hd; cases hd)))
def cl_30856 : CNF.NClause := [(35,false),(57,false),(48,false),(36,true),(114,true)]
theorem der_30856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30856 :=
  CNF.rup_sound cl_30856 [cl_24900,cl_24899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24900 v h) (hints_cons _ _ _ (der_24899 v h) (by intro d hd; cases hd)))
def cl_30857 : CNF.NClause := [(35,false),(57,false),(42,false),(36,true),(114,true)]
theorem der_30857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30857 :=
  CNF.rup_sound cl_30857 [cl_24901,cl_24899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24901 v h) (hints_cons _ _ _ (der_24899 v h) (by intro d hd; cases hd)))
def cl_30858 : CNF.NClause := [(35,false),(57,false),(48,true),(36,true),(114,true)]
theorem der_30858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30858 :=
  CNF.rup_sound cl_30858 [cl_24902,cl_30857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24902 v h) (hints_cons _ _ _ (der_30857 v h) (by intro d hd; cases hd)))
def cl_30859 : CNF.NClause := [(35,false),(48,false),(54,false),(36,true),(114,true)]
theorem der_30859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30859 :=
  CNF.rup_sound cl_30859 [cl_24904,cl_24903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24904 v h) (hints_cons _ _ _ (der_24903 v h) (by intro d hd; cases hd)))
def cl_30860 : CNF.NClause := [(35,false),(42,false),(54,false),(36,true),(114,true)]
theorem der_30860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30860 :=
  CNF.rup_sound cl_30860 [cl_24905,cl_30859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24905 v h) (hints_cons _ _ _ (der_30859 v h) (by intro d hd; cases hd)))
def cl_30861 : CNF.NClause := [(35,false),(54,false),(42,true),(36,true),(114,true)]
theorem der_30861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30861 :=
  CNF.rup_sound cl_30861 [cl_24906,cl_30859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24906 v h) (hints_cons _ _ _ (der_30859 v h) (by intro d hd; cases hd)))
def cl_30863 : CNF.NClause := [(35,false),(48,false),(42,true),(36,true),(114,true)]
theorem der_30863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30863 :=
  CNF.rup_sound cl_30863 [cl_24908,cl_30856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24908 v h) (hints_cons _ _ _ (der_30856 v h) (by intro d hd; cases hd)))
def cl_30864 : CNF.NClause := [(35,false),(42,false),(48,true),(36,true),(114,true)]
theorem der_30864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30864 :=
  CNF.rup_sound cl_30864 [cl_24909,cl_30860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24909 v h) (hints_cons _ _ _ (der_30860 v h) (by intro d hd; cases hd)))
def cl_30865 : CNF.NClause := [(58,false),(52,false),(34,false),(36,true),(116,true)]
theorem der_30865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30865 :=
  CNF.rup_sound cl_30865 [cl_24913,cl_24912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24913 v h) (hints_cons _ _ _ (der_24912 v h) (by intro d hd; cases hd)))
def cl_30866 : CNF.NClause := [(58,false),(34,false),(36,true),(43,true),(116,true)]
theorem der_30866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30866 :=
  CNF.rup_sound cl_30866 [cl_24917,cl_24915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24917 v h) (hints_cons _ _ _ (der_24915 v h) (by intro d hd; cases hd)))
def cl_30867 : CNF.NClause := [(50,false),(52,false),(34,false),(36,true),(116,true)]
theorem der_30867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30867 :=
  CNF.rup_sound cl_30867 [cl_24919,cl_24918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24919 v h) (hints_cons _ _ _ (der_24918 v h) (by intro d hd; cases hd)))
def cl_30868 : CNF.NClause := [(52,false),(116,true),(34,false),(36,true),(43,false)]
theorem der_30868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30868 :=
  CNF.rup_sound cl_30868 [cl_24920,cl_30867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24920 v h) (hints_cons _ _ _ (der_30867 v h) (by intro d hd; cases hd)))
def cl_30869 : CNF.NClause := [(52,false),(34,false),(36,true),(50,true),(116,true)]
theorem der_30869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30869 :=
  CNF.rup_sound cl_30869 [cl_24921,cl_30868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24921 v h) (hints_cons _ _ _ (der_30868 v h) (by intro d hd; cases hd)))
def cl_30870 : CNF.NClause := [(50,false),(34,false),(52,true),(43,false),(116,true)]
theorem der_30870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30870 :=
  CNF.rup_sound cl_30870 [cl_24922,cl_24914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24922 v h) (hints_cons _ _ _ (der_24914 v h) (by intro d hd; cases hd)))
def cl_30871 : CNF.NClause := [(50,false),(34,false),(36,true),(43,true),(116,true)]
theorem der_30871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30871 :=
  CNF.rup_sound cl_30871 [cl_24923,cl_30866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24923 v h) (hints_cons _ _ _ (der_30866 v h) (by intro d hd; cases hd)))
def cl_30872 : CNF.NClause := [(34,false),(36,true),(43,false),(50,true),(116,true)]
theorem der_30872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30872 :=
  CNF.rup_sound cl_30872 [cl_24924,cl_24916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24924 v h) (hints_cons _ _ _ (der_24916 v h) (by intro d hd; cases hd)))
def cl_30873 : CNF.NClause := [(31,false),(92,false),(88,false),(90,false),(91,true)]
theorem der_30873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30873 :=
  CNF.rup_sound cl_30873 [cl_24926,cl_24682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24926 v h) (hints_cons _ _ _ (der_24682 v h) (by intro d hd; cases hd)))
def cl_30874 : CNF.NClause := [(31,false),(92,false),(88,false),(87,false),(91,true)]
theorem der_30874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30874 :=
  CNF.rup_sound cl_30874 [cl_24927,cl_30712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24927 v h) (hints_cons _ _ _ (der_30712 v h) (by intro d hd; cases hd)))
def cl_30875 : CNF.NClause := [(31,false),(91,false),(88,false),(89,true),(92,true)]
theorem der_30875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30875 :=
  CNF.rup_sound cl_30875 [cl_24929,cl_24679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24929 v h) (hints_cons _ _ _ (der_24679 v h) (by intro d hd; cases hd)))
def cl_30876 : CNF.NClause := [(31,false),(90,false),(88,false),(89,true),(91,true)]
theorem der_30876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30876 :=
  CNF.rup_sound cl_30876 [cl_24930,cl_30873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24930 v h) (hints_cons _ _ _ (der_30873 v h) (by intro d hd; cases hd)))
def cl_30877 : CNF.NClause := [(31,false),(92,true),(90,true),(88,false),(91,true)]
theorem der_30877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30877 :=
  CNF.rup_sound cl_30877 [cl_24931,cl_30711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24931 v h) (hints_cons _ _ _ (der_30711 v h) (by intro d hd; cases hd)))
def cl_30878 : CNF.NClause := [(31,false),(92,false),(88,false),(90,false),(87,false)]
theorem der_30878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30878 :=
  CNF.rup_sound cl_30878 [cl_24932,cl_30874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24932 v h) (hints_cons _ _ _ (der_30874 v h) (by intro d hd; cases hd)))
def cl_30879 : CNF.NClause := [(31,false),(88,false),(90,false),(89,true),(87,true)]
theorem der_30879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30879 :=
  CNF.rup_sound cl_30879 [cl_24933,cl_30876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24933 v h) (hints_cons _ _ _ (der_30876 v h) (by intro d hd; cases hd)))
def cl_30881 : CNF.NClause := [(31,false),(92,false),(90,false),(91,true),(87,true)]
theorem der_30881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30881 :=
  CNF.rup_sound cl_30881 [cl_24938,cl_24682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24938 v h) (hints_cons _ _ _ (der_24682 v h) (by intro d hd; cases hd)))
def cl_30882 : CNF.NClause := [(31,false),(90,true),(92,false),(88,true),(87,true)]
theorem der_30882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30882 :=
  CNF.rup_sound cl_30882 [cl_24940,cl_24939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24940 v h) (hints_cons _ _ _ (der_24939 v h) (by intro d hd; cases hd)))
def cl_30883 : CNF.NClause := [(31,false),(91,false),(90,false),(92,true),(87,true)]
theorem der_30883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30883 :=
  CNF.rup_sound cl_30883 [cl_24942,cl_24941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24942 v h) (hints_cons _ _ _ (der_24941 v h) (by intro d hd; cases hd)))
def cl_30886 : CNF.NClause := [(31,false),(90,false),(89,false),(91,true),(87,true)]
theorem der_30886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30886 :=
  CNF.rup_sound cl_30886 [cl_24945,cl_30881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24945 v h) (hints_cons _ _ _ (der_30881 v h) (by intro d hd; cases hd)))
def cl_30887 : CNF.NClause := [(31,false),(89,true),(90,false),(91,true),(87,true)]
theorem der_30887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30887 :=
  CNF.rup_sound cl_30887 [cl_24946,cl_30881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24946 v h) (hints_cons _ _ _ (der_30881 v h) (by intro d hd; cases hd)))
def cl_30888 : CNF.NClause := [(31,false),(90,true),(92,true),(89,false),(87,true)]
theorem der_30888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30888 :=
  CNF.rup_sound cl_30888 [cl_24947,cl_30711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24947 v h) (hints_cons _ _ _ (der_30711 v h) (by intro d hd; cases hd)))
def cl_30889 : CNF.NClause := [(31,false),(92,true),(90,true),(89,true),(87,true)]
theorem der_30889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30889 :=
  CNF.rup_sound cl_30889 [cl_24948,cl_30708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24948 v h) (hints_cons _ _ _ (der_30708 v h) (by intro d hd; cases hd)))
def cl_30890 : CNF.NClause := [(31,false),(90,false),(91,false),(92,false),(87,false)]
theorem der_30890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30890 :=
  CNF.rup_sound cl_30890 [cl_24950,cl_30878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24950 v h) (hints_cons _ _ _ (der_30878 v h) (by intro d hd; cases hd)))
def cl_30891 : CNF.NClause := [(31,false),(92,false),(91,false),(90,true),(88,true)]
theorem der_30891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30891 :=
  CNF.rup_sound cl_30891 [cl_24952,cl_24951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24952 v h) (hints_cons _ _ _ (der_24951 v h) (by intro d hd; cases hd)))
def cl_30892 : CNF.NClause := [(31,false),(91,true),(90,false),(89,false),(92,false)]
theorem der_30892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30892 :=
  CNF.rup_sound cl_30892 [cl_24953,cl_30881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24953 v h) (hints_cons _ _ _ (der_30881 v h) (by intro d hd; cases hd)))
def cl_30893 : CNF.NClause := [(31,false),(92,false),(90,false),(89,true),(91,true)]
theorem der_30893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30893 :=
  CNF.rup_sound cl_30893 [cl_24954,cl_30881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24954 v h) (hints_cons _ _ _ (der_30881 v h) (by intro d hd; cases hd)))
def cl_30894 : CNF.NClause := [(31,false),(92,false),(89,false),(87,false),(91,true)]
theorem der_30894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30894 :=
  CNF.rup_sound cl_30894 [cl_24955,cl_30874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24955 v h) (hints_cons _ _ _ (der_30874 v h) (by intro d hd; cases hd)))
def cl_30895 : CNF.NClause := [(31,false),(92,false),(87,false),(90,true),(91,true)]
theorem der_30895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30895 :=
  CNF.rup_sound cl_30895 [cl_24956,cl_30894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24956 v h) (hints_cons _ _ _ (der_30894 v h) (by intro d hd; cases hd)))
def cl_30896 : CNF.NClause := [(31,false),(90,false),(91,false),(89,false),(92,true)]
theorem der_30896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30896 :=
  CNF.rup_sound cl_30896 [cl_24957,cl_24941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24957 v h) (hints_cons _ _ _ (der_24941 v h) (by intro d hd; cases hd)))
def cl_30897 : CNF.NClause := [(31,false),(91,false),(90,false),(89,true),(92,true)]
theorem der_30897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30897 :=
  CNF.rup_sound cl_30897 [cl_24958,cl_30883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24958 v h) (hints_cons _ _ _ (der_30883 v h) (by intro d hd; cases hd)))
def cl_30898 : CNF.NClause := [(31,false),(89,false),(90,true),(91,false),(88,true)]
theorem der_30898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30898 :=
  CNF.rup_sound cl_30898 [cl_24959,cl_30891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24959 v h) (hints_cons _ _ _ (der_30891 v h) (by intro d hd; cases hd)))
def cl_30899 : CNF.NClause := [(31,false),(91,false),(87,false),(89,true),(92,true)]
theorem der_30899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30899 :=
  CNF.rup_sound cl_30899 [cl_24960,cl_30875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24960 v h) (hints_cons _ _ _ (der_30875 v h) (by intro d hd; cases hd)))
def cl_30900 : CNF.NClause := [(31,false),(90,false),(89,false),(92,true),(91,true)]
theorem der_30900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30900 :=
  CNF.rup_sound cl_30900 [cl_24961,cl_30886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24961 v h) (hints_cons _ _ _ (der_30886 v h) (by intro d hd; cases hd)))
def cl_30901 : CNF.NClause := [(31,false),(92,true),(90,true),(89,false),(91,true)]
theorem der_30901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30901 :=
  CNF.rup_sound cl_30901 [cl_24963,cl_30888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24963 v h) (hints_cons _ _ _ (der_30888 v h) (by intro d hd; cases hd)))
def cl_30902 : CNF.NClause := [(31,false),(90,true),(87,false),(92,true),(91,true)]
theorem der_30902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30902 :=
  CNF.rup_sound cl_30902 [cl_24964,cl_30901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24964 v h) (hints_cons _ _ _ (der_30901 v h) (by intro d hd; cases hd)))
def cl_30903 : CNF.NClause := [(31,false),(92,false),(88,false),(90,false),(89,false)]
theorem der_30903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30903 :=
  CNF.rup_sound cl_30903 [cl_24965,cl_30892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24965 v h) (hints_cons _ _ _ (der_30892 v h) (by intro d hd; cases hd)))
def cl_30904 : CNF.NClause := [(61,false),(77,false),(72,false),(67,false),(82,false)]
theorem der_30904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30904 :=
  CNF.rup_sound cl_30904 [cl_24966,cl_23689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24966 v h) (hints_cons _ _ _ (der_23689 v h) (by intro d hd; cases hd)))
def cl_30905 : CNF.NClause := [(31,false),(90,true),(91,false),(89,true),(87,true)]
theorem der_30905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30905 :=
  CNF.rup_sound cl_30905 [cl_24967,cl_30889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24967 v h) (hints_cons _ _ _ (der_30889 v h) (by intro d hd; cases hd)))
def cl_30906 : CNF.NClause := [(61,false),(77,false),(67,false),(62,false),(82,true)]
theorem der_30906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30906 :=
  CNF.rup_sound cl_30906 [cl_24970,cl_30253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24970 v h) (hints_cons _ _ _ (der_30253 v h) (by intro d hd; cases hd)))
def cl_30907 : CNF.NClause := [(61,false),(77,false),(67,false),(62,false),(87,false)]
theorem der_30907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30907 :=
  CNF.rup_sound cl_30907 [cl_24971,cl_30906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24971 v h) (hints_cons _ _ _ (der_30906 v h) (by intro d hd; cases hd)))
def cl_30908 : CNF.NClause := [(61,false),(77,false),(67,false),(87,false),(82,false)]
theorem der_30908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30908 :=
  CNF.rup_sound cl_30908 [cl_24972,cl_30907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24972 v h) (hints_cons _ _ _ (der_30907 v h) (by intro d hd; cases hd)))
def cl_30909 : CNF.NClause := [(61,false),(77,false),(67,false),(87,false),(82,true)]
theorem der_30909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30909 :=
  CNF.rup_sound cl_30909 [cl_24974,cl_30907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24974 v h) (hints_cons _ _ _ (der_30907 v h) (by intro d hd; cases hd)))
def cl_30910 : CNF.NClause := [(61,false),(77,false),(62,true),(67,false),(82,false)]
theorem der_30910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30910 :=
  CNF.rup_sound cl_30910 [cl_24976,cl_30908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24976 v h) (hints_cons _ _ _ (der_30908 v h) (by intro d hd; cases hd)))
def cl_30911 : CNF.NClause := [(61,false),(67,false),(72,true),(62,true),(82,false)]
theorem der_30911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30911 :=
  CNF.rup_sound cl_30911 [cl_24977,cl_30910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24977 v h) (hints_cons _ _ _ (der_30910 v h) (by intro d hd; cases hd)))
def cl_30912 : CNF.NClause := [(61,false),(62,true),(77,false),(67,false),(82,true)]
theorem der_30912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30912 :=
  CNF.rup_sound cl_30912 [cl_24978,cl_30909] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24978 v h) (hints_cons _ _ _ (der_30909 v h) (by intro d hd; cases hd)))
def cl_30913 : CNF.NClause := [(61,false),(77,true),(67,false),(82,true),(87,true)]
theorem der_30913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30913 :=
  CNF.rup_sound cl_30913 [cl_24979,cl_24969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24979 v h) (hints_cons _ _ _ (der_24969 v h) (by intro d hd; cases hd)))
def cl_30914 : CNF.NClause := [(61,false),(72,true),(67,false),(87,false),(82,false)]
theorem der_30914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30914 :=
  CNF.rup_sound cl_30914 [cl_24980,cl_30908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24980 v h) (hints_cons _ _ _ (der_30908 v h) (by intro d hd; cases hd)))
def cl_30915 : CNF.NClause := [(61,false),(62,false),(67,false),(87,false),(82,true)]
theorem der_30915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30915 :=
  CNF.rup_sound cl_30915 [cl_24981,cl_30909] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24981 v h) (hints_cons _ _ _ (der_30909 v h) (by intro d hd; cases hd)))
def cl_30916 : CNF.NClause := [(61,false),(67,false),(72,true),(82,false),(87,true)]
theorem der_30916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30916 :=
  CNF.rup_sound cl_30916 [cl_24982,cl_30911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24982 v h) (hints_cons _ _ _ (der_30911 v h) (by intro d hd; cases hd)))
def cl_30918 : CNF.NClause := [(61,false),(62,false),(87,false),(82,false),(67,true)]
theorem der_30918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30918 :=
  CNF.rup_sound cl_30918 [cl_24986,cl_24985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24986 v h) (hints_cons _ _ _ (der_24985 v h) (by intro d hd; cases hd)))
def cl_30919 : CNF.NClause := [(61,false),(77,false),(72,false),(62,false),(87,false)]
theorem der_30919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30919 :=
  CNF.rup_sound cl_30919 [cl_24987,cl_30907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24987 v h) (hints_cons _ _ _ (der_30907 v h) (by intro d hd; cases hd)))
def cl_30920 : CNF.NClause := [(61,false),(62,false),(77,false),(72,true),(87,false)]
theorem der_30920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30920 :=
  CNF.rup_sound cl_30920 [cl_24988,cl_30907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24988 v h) (hints_cons _ _ _ (der_30907 v h) (by intro d hd; cases hd)))
def cl_30921 : CNF.NClause := [(61,false),(72,false),(62,false),(87,false),(82,true)]
theorem der_30921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30921 :=
  CNF.rup_sound cl_30921 [cl_24989,cl_30919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24989 v h) (hints_cons _ _ _ (der_30919 v h) (by intro d hd; cases hd)))
def cl_30922 : CNF.NClause := [(61,false),(62,false),(72,true),(87,false),(67,true)]
theorem der_30922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30922 :=
  CNF.rup_sound cl_30922 [cl_24990,cl_30920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24990 v h) (hints_cons _ _ _ (der_30920 v h) (by intro d hd; cases hd)))
def cl_30923 : CNF.NClause := [(61,false),(77,false),(72,false),(62,false),(82,false)]
theorem der_30923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30923 :=
  CNF.rup_sound cl_30923 [cl_24991,cl_30904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24991 v h) (hints_cons _ _ _ (der_30904 v h) (by intro d hd; cases hd)))
def cl_30924 : CNF.NClause := [(61,false),(62,false),(77,false),(82,false),(67,true)]
theorem der_30924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30924 :=
  CNF.rup_sound cl_30924 [cl_24992,cl_30923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24992 v h) (hints_cons _ _ _ (der_30923 v h) (by intro d hd; cases hd)))
def cl_30925 : CNF.NClause := [(61,false),(72,false),(62,false),(82,false),(87,true)]
theorem der_30925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30925 :=
  CNF.rup_sound cl_30925 [cl_24993,cl_30923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24993 v h) (hints_cons _ _ _ (der_30923 v h) (by intro d hd; cases hd)))
def cl_30926 : CNF.NClause := [(61,false),(62,false),(72,true),(82,false),(67,true)]
theorem der_30926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30926 :=
  CNF.rup_sound cl_30926 [cl_24994,cl_30924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24994 v h) (hints_cons _ _ _ (der_30924 v h) (by intro d hd; cases hd)))
def cl_30927 : CNF.NClause := [(61,false),(77,false),(72,false),(62,false),(82,true)]
theorem der_30927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30927 :=
  CNF.rup_sound cl_30927 [cl_24995,cl_30253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24995 v h) (hints_cons _ _ _ (der_30253 v h) (by intro d hd; cases hd)))
def cl_30929 : CNF.NClause := [(61,false),(72,false),(62,false),(82,true),(87,true)]
theorem der_30929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30929 :=
  CNF.rup_sound cl_30929 [cl_24997,cl_30927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24997 v h) (hints_cons _ _ _ (der_30927 v h) (by intro d hd; cases hd)))
def cl_30930 : CNF.NClause := [(61,false),(72,true),(62,false),(67,true),(87,true)]
theorem der_30930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30930 :=
  CNF.rup_sound cl_30930 [cl_24998,cl_30926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24998 v h) (hints_cons _ _ _ (der_30926 v h) (by intro d hd; cases hd)))
def cl_30931 : CNF.NClause := [(61,false),(82,false),(72,false),(87,false),(77,false)]
theorem der_30931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30931 :=
  CNF.rup_sound cl_30931 [cl_24999,cl_30908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24999 v h) (hints_cons _ _ _ (der_30908 v h) (by intro d hd; cases hd)))
def cl_30932 : CNF.NClause := [(61,false),(72,true),(77,false),(87,false),(82,false)]
theorem der_30932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30932 :=
  CNF.rup_sound cl_30932 [cl_25000,cl_30914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25000 v h) (hints_cons _ _ _ (der_30914 v h) (by intro d hd; cases hd)))
def cl_30933 : CNF.NClause := [(61,false),(62,true),(72,false),(87,false),(82,false)]
theorem der_30933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30933 :=
  CNF.rup_sound cl_30933 [cl_25001,cl_30931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25001 v h) (hints_cons _ _ _ (der_30931 v h) (by intro d hd; cases hd)))
def cl_30934 : CNF.NClause := [(61,false),(62,true),(77,true),(87,false),(82,false)]
theorem der_30934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30934 :=
  CNF.rup_sound cl_30934 [cl_25002,cl_30933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25002 v h) (hints_cons _ _ _ (der_30933 v h) (by intro d hd; cases hd)))
def cl_30935 : CNF.NClause := [(61,false),(77,false),(72,false),(87,false),(67,true)]
theorem der_30935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30935 :=
  CNF.rup_sound cl_30935 [cl_25003,cl_30931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25003 v h) (hints_cons _ _ _ (der_30931 v h) (by intro d hd; cases hd)))
def cl_30936 : CNF.NClause := [(61,false),(72,true),(77,false),(87,false),(67,true)]
theorem der_30936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30936 :=
  CNF.rup_sound cl_30936 [cl_25004,cl_30932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25004 v h) (hints_cons _ _ _ (der_30932 v h) (by intro d hd; cases hd)))
def cl_30937 : CNF.NClause := [(61,false),(72,false),(87,false),(82,true),(77,true)]
theorem der_30937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30937 :=
  CNF.rup_sound cl_30937 [cl_25005,cl_30048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25005 v h) (hints_cons _ _ _ (der_30048 v h) (by intro d hd; cases hd)))
def cl_30938 : CNF.NClause := [(61,false),(72,true),(87,false),(82,true),(67,true)]
theorem der_30938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30938 :=
  CNF.rup_sound cl_30938 [cl_25006,cl_30922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25006 v h) (hints_cons _ _ _ (der_30922 v h) (by intro d hd; cases hd)))
def cl_30939 : CNF.NClause := [(61,false),(82,false),(77,false),(72,false),(87,true)]
theorem der_30939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30939 :=
  CNF.rup_sound cl_30939 [cl_25007,cl_30923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25007 v h) (hints_cons _ _ _ (der_30923 v h) (by intro d hd; cases hd)))
def cl_30940 : CNF.NClause := [(61,false),(77,false),(72,true),(62,true),(82,false)]
theorem der_30940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30940 :=
  CNF.rup_sound cl_30940 [cl_25008,cl_30932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25008 v h) (hints_cons _ _ _ (der_30932 v h) (by intro d hd; cases hd)))
def cl_30941 : CNF.NClause := [(61,false),(62,true),(72,true),(82,false),(87,true)]
theorem der_30941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30941 :=
  CNF.rup_sound cl_30941 [cl_25010,cl_30940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25010 v h) (hints_cons _ _ _ (der_30940 v h) (by intro d hd; cases hd)))
def cl_30942 : CNF.NClause := [(61,false),(77,false),(72,false),(82,true),(67,true)]
theorem der_30942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30942 :=
  CNF.rup_sound cl_30942 [cl_25011,cl_30935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25011 v h) (hints_cons _ _ _ (der_30935 v h) (by intro d hd; cases hd)))
def cl_30943 : CNF.NClause := [(61,false),(77,false),(62,true),(82,true),(67,true)]
theorem der_30943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30943 :=
  CNF.rup_sound cl_30943 [cl_25012,cl_30942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25012 v h) (hints_cons _ _ _ (der_30942 v h) (by intro d hd; cases hd)))
def cl_30944 : CNF.NClause := [(61,false),(62,true),(77,true),(72,false),(82,true)]
theorem der_30944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30944 :=
  CNF.rup_sound cl_30944 [cl_25013,cl_30937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25013 v h) (hints_cons _ _ _ (der_30937 v h) (by intro d hd; cases hd)))
def cl_30945 : CNF.NClause := [(61,false),(62,true),(72,true),(82,true),(67,true)]
theorem der_30945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30945 :=
  CNF.rup_sound cl_30945 [cl_25014,cl_30943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25014 v h) (hints_cons _ _ _ (der_30943 v h) (by intro d hd; cases hd)))
def cl_30946 : CNF.NClause := [(56,false),(92,false),(62,false),(64,false),(66,false)]
theorem der_30946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30946 :=
  CNF.rup_sound cl_30946 [cl_25017,cl_30718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25017 v h) (hints_cons _ _ _ (der_30718 v h) (by intro d hd; cases hd)))
def cl_30947 : CNF.NClause := [(56,false),(62,false),(92,false),(64,false),(65,false)]
theorem der_30947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30947 :=
  CNF.rup_sound cl_30947 [cl_25019,cl_30714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25019 v h) (hints_cons _ _ _ (der_30714 v h) (by intro d hd; cases hd)))
def cl_30948 : CNF.NClause := [(56,false),(65,false),(63,true),(92,false),(62,false)]
theorem der_30948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30948 :=
  CNF.rup_sound cl_30948 [cl_25020,cl_30947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25020 v h) (hints_cons _ _ _ (der_30947 v h) (by intro d hd; cases hd)))
def cl_30949 : CNF.NClause := [(56,false),(62,false),(92,false),(63,true),(64,false)]
theorem der_30949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30949 :=
  CNF.rup_sound cl_30949 [cl_25021,cl_30946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25021 v h) (hints_cons _ _ _ (der_30946 v h) (by intro d hd; cases hd)))
def cl_30950 : CNF.NClause := [(56,false),(64,true),(65,true),(63,true),(92,false)]
theorem der_30950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30950 :=
  CNF.rup_sound cl_30950 [cl_25022,cl_25018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25022 v h) (hints_cons _ _ _ (der_25018 v h) (by intro d hd; cases hd)))
def cl_30951 : CNF.NClause := [(56,false),(62,false),(64,false),(66,false),(65,false)]
theorem der_30951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30951 :=
  CNF.rup_sound cl_30951 [cl_25023,cl_25015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25023 v h) (hints_cons _ _ _ (der_25015 v h) (by intro d hd; cases hd)))
def cl_30953 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(66,false)]
theorem der_30953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30953 :=
  CNF.rup_sound cl_30953 [cl_25025,cl_30949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25025 v h) (hints_cons _ _ _ (der_30949 v h) (by intro d hd; cases hd)))
def cl_30954 : CNF.NClause := [(56,false),(63,true),(62,false),(66,false),(92,true)]
theorem der_30954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30954 :=
  CNF.rup_sound cl_30954 [cl_25026,cl_30953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25026 v h) (hints_cons _ _ _ (der_30953 v h) (by intro d hd; cases hd)))
def cl_30955 : CNF.NClause := [(56,false),(62,false),(64,false),(65,false),(92,true)]
theorem der_30955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30955 :=
  CNF.rup_sound cl_30955 [cl_25027,cl_30714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25027 v h) (hints_cons _ _ _ (der_30714 v h) (by intro d hd; cases hd)))
def cl_30956 : CNF.NClause := [(56,false),(63,true),(62,false),(65,false),(64,true)]
theorem der_30956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30956 :=
  CNF.rup_sound cl_30956 [cl_25028,cl_30948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25028 v h) (hints_cons _ _ _ (der_30948 v h) (by intro d hd; cases hd)))
def cl_30957 : CNF.NClause := [(56,false),(63,true),(66,true),(62,false),(64,false)]
theorem der_30957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30957 :=
  CNF.rup_sound cl_30957 [cl_25029,cl_30949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25029 v h) (hints_cons _ _ _ (der_30949 v h) (by intro d hd; cases hd)))
def cl_30958 : CNF.NClause := [(56,false),(62,false),(63,true),(64,true),(92,true)]
theorem der_30958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30958 :=
  CNF.rup_sound cl_30958 [cl_25030,cl_30954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25030 v h) (hints_cons _ _ _ (der_30954 v h) (by intro d hd; cases hd)))
def cl_30959 : CNF.NClause := [(56,false),(92,false),(64,false),(66,false),(65,false)]
theorem der_30959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30959 :=
  CNF.rup_sound cl_30959 [cl_25031,cl_25015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25031 v h) (hints_cons _ _ _ (der_25015 v h) (by intro d hd; cases hd)))
def cl_30960 : CNF.NClause := [(56,false),(62,true),(92,false),(64,false),(65,false)]
theorem der_30960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30960 :=
  CNF.rup_sound cl_30960 [cl_25033,cl_30722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25033 v h) (hints_cons _ _ _ (der_30722 v h) (by intro d hd; cases hd)))
def cl_30961 : CNF.NClause := [(56,false),(62,true),(65,true),(63,true),(92,false)]
theorem der_30961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30961 :=
  CNF.rup_sound cl_30961 [cl_25034,cl_25032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25034 v h) (hints_cons _ _ _ (der_25032 v h) (by intro d hd; cases hd)))
def cl_30962 : CNF.NClause := [(56,false),(92,true),(64,false),(66,false),(65,false)]
theorem der_30962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30962 :=
  CNF.rup_sound cl_30962 [cl_25035,cl_30951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25035 v h) (hints_cons _ _ _ (der_30951 v h) (by intro d hd; cases hd)))
def cl_30963 : CNF.NClause := [(56,false),(62,true),(65,true),(63,true),(66,false)]
theorem der_30963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30963 :=
  CNF.rup_sound cl_30963 [cl_25036,cl_30719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25036 v h) (hints_cons _ _ _ (der_30719 v h) (by intro d hd; cases hd)))
def cl_30964 : CNF.NClause := [(56,false),(62,true),(64,false),(65,false),(92,true)]
theorem der_30964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30964 :=
  CNF.rup_sound cl_30964 [cl_25037,cl_30962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25037 v h) (hints_cons _ _ _ (der_30962 v h) (by intro d hd; cases hd)))
def cl_30965 : CNF.NClause := [(56,false),(62,true),(66,true),(64,false),(92,true)]
theorem der_30965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30965 :=
  CNF.rup_sound cl_30965 [cl_25038,cl_30964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25038 v h) (hints_cons _ _ _ (der_30964 v h) (by intro d hd; cases hd)))
def cl_30966 : CNF.NClause := [(51,false),(42,false),(33,false),(58,true),(100,true)]
theorem der_30966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30966 :=
  CNF.rup_sound cl_30966 [cl_25043,cl_30111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25043 v h) (hints_cons _ _ _ (der_30111 v h) (by intro d hd; cases hd)))
def cl_30967 : CNF.NClause := [(57,false),(59,false),(56,true),(60,true),(93,true)]
theorem der_30967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30967 :=
  CNF.rup_sound cl_30967 [cl_25046,cl_25040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25046 v h) (hints_cons _ _ _ (der_25040 v h) (by intro d hd; cases hd)))
def cl_30968 : CNF.NClause := [(35,false),(37,false),(46,false),(58,true),(109,true)]
theorem der_30968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30968 :=
  CNF.rup_sound cl_30968 [cl_25047,cl_30120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25047 v h) (hints_cons _ _ _ (der_30120 v h) (by intro d hd; cases hd)))
def cl_30970 : CNF.NClause := [(54,false),(45,false),(31,true),(58,true),(120,true)]
theorem der_30970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30970 :=
  CNF.rup_sound cl_30970 [cl_25052,cl_23710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25052 v h) (hints_cons _ _ _ (der_23710 v h) (by intro d hd; cases hd)))
def cl_30971 : CNF.NClause := [(51,false),(55,false),(54,true),(61,true),(98,true)]
theorem der_30971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30971 :=
  CNF.rup_sound cl_30971 [cl_25053,cl_30077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25053 v h) (hints_cons _ _ _ (der_30077 v h) (by intro d hd; cases hd)))
def cl_30972 : CNF.NClause := [(51,false),(61,true),(54,true),(53,false),(98,true)]
theorem der_30972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30972 :=
  CNF.rup_sound cl_30972 [cl_25054,cl_30971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25054 v h) (hints_cons _ _ _ (der_30971 v h) (by intro d hd; cases hd)))
def cl_30974 : CNF.NClause := [(51,false),(53,false),(55,true),(54,true),(98,true)]
theorem der_30974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30974 :=
  CNF.rup_sound cl_30974 [cl_25058,cl_30110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25058 v h) (hints_cons _ _ _ (der_30110 v h) (by intro d hd; cases hd)))
def cl_30975 : CNF.NClause := [(41,false),(50,false),(33,false),(60,false),(105,true)]
theorem der_30975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30975 :=
  CNF.rup_sound cl_30975 [cl_25059,cl_30760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25059 v h) (hints_cons _ _ _ (der_30760 v h) (by intro d hd; cases hd)))
def cl_30977 : CNF.NClause := [(32,false),(59,false),(43,false),(40,true),(112,true)]
theorem der_30977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30977 :=
  CNF.rup_sound cl_30977 [cl_25061,cl_23899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25061 v h) (hints_cons _ _ _ (der_23899 v h) (by intro d hd; cases hd)))
def cl_30978 : CNF.NClause := [(32,false),(112,true),(40,true),(54,true),(43,false)]
theorem der_30978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30978 :=
  CNF.rup_sound cl_30978 [cl_25062,cl_30977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25062 v h) (hints_cons _ _ _ (der_30977 v h) (by intro d hd; cases hd)))
def cl_30979 : CNF.NClause := [(35,false),(57,false),(48,false),(42,false),(114,true)]
theorem der_30979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30979 :=
  CNF.rup_sound cl_30979 [cl_25064,cl_30857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25064 v h) (hints_cons _ _ _ (der_30857 v h) (by intro d hd; cases hd)))
def cl_30980 : CNF.NClause := [(35,false),(48,false),(42,false),(54,true),(114,true)]
theorem der_30980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30980 :=
  CNF.rup_sound cl_30980 [cl_25065,cl_30979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25065 v h) (hints_cons _ _ _ (der_30979 v h) (by intro d hd; cases hd)))
def cl_30981 : CNF.NClause := [(58,false),(45,false),(31,true),(54,true),(120,true)]
theorem der_30981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30981 :=
  CNF.rup_sound cl_30981 [cl_25068,cl_23708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25068 v h) (hints_cons _ _ _ (der_23708 v h) (by intro d hd; cases hd)))
def cl_30982 : CNF.NClause := [(38,false),(45,false),(31,true),(58,true),(120,true)]
theorem der_30982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30982 :=
  CNF.rup_sound cl_30982 [cl_25069,cl_25067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25069 v h) (hints_cons _ _ _ (der_25067 v h) (by intro d hd; cases hd)))
def cl_30983 : CNF.NClause := [(45,false),(47,false),(31,true),(38,true),(120,true)]
theorem der_30983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30983 :=
  CNF.rup_sound cl_30983 [cl_25070,cl_23711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25070 v h) (hints_cons _ _ _ (der_23711 v h) (by intro d hd; cases hd)))
def cl_30984 : CNF.NClause := [(58,false),(54,false),(45,true),(31,true),(120,true)]
theorem der_30984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30984 :=
  CNF.rup_sound cl_30984 [cl_25071,cl_23714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25071 v h) (hints_cons _ _ _ (der_23714 v h) (by intro d hd; cases hd)))
def cl_30985 : CNF.NClause := [(54,false),(38,false),(31,true),(47,true),(120,true)]
theorem der_30985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30985 :=
  CNF.rup_sound cl_30985 [cl_25072,cl_25051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25072 v h) (hints_cons _ _ _ (der_25051 v h) (by intro d hd; cases hd)))
def cl_30986 : CNF.NClause := [(54,false),(45,false),(47,false),(31,true),(120,true)]
theorem der_30986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30986 :=
  CNF.rup_sound cl_30986 [cl_25073,cl_30983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25073 v h) (hints_cons _ _ _ (der_30983 v h) (by intro d hd; cases hd)))
def cl_30989 : CNF.NClause := [(32,false),(35,false),(61,false),(31,false),(118,true)]
theorem der_30989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30989 :=
  CNF.rup_sound cl_30989 [cl_25079,cl_25077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25079 v h) (hints_cons _ _ _ (der_25077 v h) (by intro d hd; cases hd)))
def cl_30992 : CNF.NClause := [(32,false),(61,false),(34,false),(31,false),(118,true)]
theorem der_30992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30992 :=
  CNF.rup_sound cl_30992 [cl_25083,cl_25081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25083 v h) (hints_cons _ _ _ (der_25081 v h) (by intro d hd; cases hd)))
def cl_30994 : CNF.NClause := [(32,false),(61,false),(33,false),(31,false),(118,true)]
theorem der_30994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30994 :=
  CNF.rup_sound cl_30994 [cl_25085,cl_30992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25085 v h) (hints_cons _ _ _ (der_30992 v h) (by intro d hd; cases hd)))
def cl_30998 : CNF.NClause := [(35,false),(34,false),(31,false),(33,true),(118,true)]
theorem der_30998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30998 :=
  CNF.rup_sound cl_30998 [cl_25092,cl_25091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25092 v h) (hints_cons _ _ _ (der_25091 v h) (by intro d hd; cases hd)))
def cl_30999 : CNF.NClause := [(35,false),(31,false),(33,false),(34,true),(118,true)]
theorem der_30999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30999 :=
  CNF.rup_sound cl_30999 [cl_25094,cl_25093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25094 v h) (hints_cons _ _ _ (der_25093 v h) (by intro d hd; cases hd)))
def cl_31000 : CNF.NClause := [(32,false),(35,false),(31,false),(34,true),(118,true)]
theorem der_31000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31000 :=
  CNF.rup_sound cl_31000 [cl_25095,cl_30989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25095 v h) (hints_cons _ _ _ (der_30989 v h) (by intro d hd; cases hd)))
def cl_31003 : CNF.NClause := [(32,false),(34,false),(31,false),(33,true),(118,true)]
theorem der_31003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31003 :=
  CNF.rup_sound cl_31003 [cl_25099,cl_25091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25099 v h) (hints_cons _ _ _ (der_25091 v h) (by intro d hd; cases hd)))
def cl_31005 : CNF.NClause := [(32,false),(31,false),(33,false),(34,true),(118,true)]
theorem der_31005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31005 :=
  CNF.rup_sound cl_31005 [cl_25101,cl_30994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25101 v h) (hints_cons _ _ _ (der_30994 v h) (by intro d hd; cases hd)))
def cl_31007 : CNF.NClause := [(32,false),(31,false),(34,true),(33,true),(118,true)]
theorem der_31007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31007 :=
  CNF.rup_sound cl_31007 [cl_25103,cl_31000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25103 v h) (hints_cons _ _ _ (der_31000 v h) (by intro d hd; cases hd)))
def cl_31009 : CNF.NClause := [(60,false),(52,false),(44,false),(31,false),(119,true)]
theorem der_31009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31009 :=
  CNF.rup_sound cl_31009 [cl_25108,cl_25107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25108 v h) (hints_cons _ _ _ (der_25107 v h) (by intro d hd; cases hd)))
def cl_31012 : CNF.NClause := [(48,false),(60,false),(44,false),(31,false),(119,true)]
theorem der_31012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31012 :=
  CNF.rup_sound cl_31012 [cl_25112,cl_25111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25112 v h) (hints_cons _ _ _ (der_25111 v h) (by intro d hd; cases hd)))
def cl_31014 : CNF.NClause := [(60,false),(40,false),(44,false),(31,false),(119,true)]
theorem der_31014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31014 :=
  CNF.rup_sound cl_31014 [cl_25115,cl_25107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25115 v h) (hints_cons _ _ _ (der_25107 v h) (by intro d hd; cases hd)))
def cl_31015 : CNF.NClause := [(60,false),(44,false),(31,false),(40,true),(119,true)]
theorem der_31015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31015 :=
  CNF.rup_sound cl_31015 [cl_25116,cl_31009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25116 v h) (hints_cons _ _ _ (der_31009 v h) (by intro d hd; cases hd)))
def cl_31016 : CNF.NClause := [(60,false),(40,false),(44,true),(52,true),(119,true)]
theorem der_31016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31016 :=
  CNF.rup_sound cl_31016 [cl_25117,cl_25113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25117 v h) (hints_cons _ _ _ (der_25113 v h) (by intro d hd; cases hd)))
def cl_31018 : CNF.NClause := [(48,false),(40,false),(52,false),(31,false),(119,true)]
theorem der_31018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31018 :=
  CNF.rup_sound cl_31018 [cl_25121,cl_25119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25121 v h) (hints_cons _ _ _ (der_25119 v h) (by intro d hd; cases hd)))
def cl_31019 : CNF.NClause := [(48,false),(52,false),(31,false),(44,true),(119,true)]
theorem der_31019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31019 :=
  CNF.rup_sound cl_31019 [cl_25122,cl_31018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25122 v h) (hints_cons _ _ _ (der_31018 v h) (by intro d hd; cases hd)))
def cl_31020 : CNF.NClause := [(40,false),(52,false),(44,false),(31,false),(119,true)]
theorem der_31020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31020 :=
  CNF.rup_sound cl_31020 [cl_25123,cl_25119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25123 v h) (hints_cons _ _ _ (der_25119 v h) (by intro d hd; cases hd)))
def cl_31021 : CNF.NClause := [(52,false),(44,false),(31,false),(48,true),(119,true)]
theorem der_31021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31021 :=
  CNF.rup_sound cl_31021 [cl_25124,cl_31009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25124 v h) (hints_cons _ _ _ (der_31009 v h) (by intro d hd; cases hd)))
def cl_31022 : CNF.NClause := [(40,false),(52,false),(31,false),(48,true),(119,true)]
theorem der_31022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31022 :=
  CNF.rup_sound cl_31022 [cl_25125,cl_31020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25125 v h) (hints_cons _ _ _ (der_31020 v h) (by intro d hd; cases hd)))
def cl_31023 : CNF.NClause := [(52,false),(31,false),(44,true),(48,true),(119,true)]
theorem der_31023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31023 :=
  CNF.rup_sound cl_31023 [cl_25126,cl_31022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25126 v h) (hints_cons _ _ _ (der_31022 v h) (by intro d hd; cases hd)))
def cl_31024 : CNF.NClause := [(48,false),(40,false),(44,false),(31,false),(119,true)]
theorem der_31024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31024 :=
  CNF.rup_sound cl_31024 [cl_25127,cl_31020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25127 v h) (hints_cons _ _ _ (der_31020 v h) (by intro d hd; cases hd)))
def cl_31025 : CNF.NClause := [(48,false),(44,false),(31,false),(52,true),(119,true)]
theorem der_31025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31025 :=
  CNF.rup_sound cl_31025 [cl_25128,cl_31024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25128 v h) (hints_cons _ _ _ (der_31024 v h) (by intro d hd; cases hd)))
def cl_31026 : CNF.NClause := [(48,false),(40,false),(44,true),(52,true),(119,true)]
theorem der_31026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31026 :=
  CNF.rup_sound cl_31026 [cl_25129,cl_25113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25129 v h) (hints_cons _ _ _ (der_25113 v h) (by intro d hd; cases hd)))
def cl_31028 : CNF.NClause := [(40,false),(44,false),(31,false),(48,true),(119,true)]
theorem der_31028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31028 :=
  CNF.rup_sound cl_31028 [cl_25131,cl_31014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25131 v h) (hints_cons _ _ _ (der_31014 v h) (by intro d hd; cases hd)))
def cl_31029 : CNF.NClause := [(44,false),(31,false),(48,true),(60,true),(119,true)]
theorem der_31029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31029 :=
  CNF.rup_sound cl_31029 [cl_25132,cl_31021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25132 v h) (hints_cons _ _ _ (der_31021 v h) (by intro d hd; cases hd)))
def cl_31031 : CNF.NClause := [(58,false),(54,false),(45,false),(47,false),(120,true)]
theorem der_31031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31031 :=
  CNF.rup_sound cl_31031 [cl_25135,cl_25134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25135 v h) (hints_cons _ _ _ (der_25134 v h) (by intro d hd; cases hd)))
def cl_31032 : CNF.NClause := [(58,false),(54,false),(38,false),(47,false),(120,true)]
theorem der_31032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31032 :=
  CNF.rup_sound cl_31032 [cl_25136,cl_25134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25136 v h) (hints_cons _ _ _ (der_25134 v h) (by intro d hd; cases hd)))
def cl_31034 : CNF.NClause := [(58,false),(54,false),(45,false),(31,false),(120,true)]
theorem der_31034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31034 :=
  CNF.rup_sound cl_31034 [cl_25139,cl_25138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25139 v h) (hints_cons _ _ _ (der_25138 v h) (by intro d hd; cases hd)))
def cl_31035 : CNF.NClause := [(58,false),(54,false),(38,false),(45,true),(120,true)]
theorem der_31035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31035 :=
  CNF.rup_sound cl_31035 [cl_25140,cl_31032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25140 v h) (hints_cons _ _ _ (der_31032 v h) (by intro d hd; cases hd)))
def cl_31036 : CNF.NClause := [(58,false),(54,false),(45,true),(38,true),(120,true)]
theorem der_31036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31036 :=
  CNF.rup_sound cl_31036 [cl_25141,cl_30984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25141 v h) (hints_cons _ _ _ (der_30984 v h) (by intro d hd; cases hd)))
def cl_31037 : CNF.NClause := [(58,false),(38,false),(45,false),(47,false),(120,true)]
theorem der_31037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31037 :=
  CNF.rup_sound cl_31037 [cl_25142,cl_25134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25142 v h) (hints_cons _ _ _ (der_25134 v h) (by intro d hd; cases hd)))
def cl_31038 : CNF.NClause := [(58,false),(45,false),(47,false),(38,true),(120,true)]
theorem der_31038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31038 :=
  CNF.rup_sound cl_31038 [cl_25143,cl_31031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25143 v h) (hints_cons _ _ _ (der_31031 v h) (by intro d hd; cases hd)))
def cl_31041 : CNF.NClause := [(58,false),(38,false),(45,false),(54,true),(120,true)]
theorem der_31041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31041 :=
  CNF.rup_sound cl_31041 [cl_25146,cl_31037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25146 v h) (hints_cons _ _ _ (der_31037 v h) (by intro d hd; cases hd)))
def cl_31042 : CNF.NClause := [(58,false),(45,false),(38,true),(54,true),(120,true)]
theorem der_31042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31042 :=
  CNF.rup_sound cl_31042 [cl_25147,cl_31038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25147 v h) (hints_cons _ _ _ (der_31038 v h) (by intro d hd; cases hd)))
def cl_31043 : CNF.NClause := [(58,false),(38,false),(45,true),(47,true),(120,true)]
theorem der_31043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31043 :=
  CNF.rup_sound cl_31043 [cl_25148,cl_31035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25148 v h) (hints_cons _ _ _ (der_31035 v h) (by intro d hd; cases hd)))
def cl_31045 : CNF.NClause := [(54,false),(38,false),(45,false),(47,false),(120,true)]
theorem der_31045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31045 :=
  CNF.rup_sound cl_31045 [cl_25150,cl_31032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25150 v h) (hints_cons _ _ _ (der_31032 v h) (by intro d hd; cases hd)))
def cl_31046 : CNF.NClause := [(54,false),(45,false),(47,false),(58,true),(120,true)]
theorem der_31046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31046 :=
  CNF.rup_sound cl_31046 [cl_25151,cl_31045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25151 v h) (hints_cons _ _ _ (der_31045 v h) (by intro d hd; cases hd)))
def cl_31049 : CNF.NClause := [(54,false),(38,false),(45,false),(58,true),(120,true)]
theorem der_31049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31049 :=
  CNF.rup_sound cl_31049 [cl_25154,cl_31045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25154 v h) (hints_cons _ _ _ (der_31045 v h) (by intro d hd; cases hd)))
def cl_31050 : CNF.NClause := [(54,false),(45,false),(38,true),(58,true),(120,true)]
theorem der_31050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31050 :=
  CNF.rup_sound cl_31050 [cl_25155,cl_31046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25155 v h) (hints_cons _ _ _ (der_31046 v h) (by intro d hd; cases hd)))
def cl_31051 : CNF.NClause := [(54,false),(38,false),(45,true),(47,true),(120,true)]
theorem der_31051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31051 :=
  CNF.rup_sound cl_31051 [cl_25156,cl_31035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25156 v h) (hints_cons _ _ _ (der_31035 v h) (by intro d hd; cases hd)))
def cl_31053 : CNF.NClause := [(38,false),(45,false),(47,false),(54,true),(120,true)]
theorem der_31053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31053 :=
  CNF.rup_sound cl_31053 [cl_25158,cl_31037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25158 v h) (hints_cons _ _ _ (der_31037 v h) (by intro d hd; cases hd)))
def cl_31054 : CNF.NClause := [(45,false),(47,false),(38,true),(54,true),(120,true)]
theorem der_31054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31054 :=
  CNF.rup_sound cl_31054 [cl_25159,cl_23711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25159 v h) (hints_cons _ _ _ (der_23711 v h) (by intro d hd; cases hd)))
def cl_31055 : CNF.NClause := [(38,false),(47,false),(45,true),(54,true),(120,true)]
theorem der_31055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31055 :=
  CNF.rup_sound cl_31055 [cl_25160,cl_23705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25160 v h) (hints_cons _ _ _ (der_23705 v h) (by intro d hd; cases hd)))
def cl_31057 : CNF.NClause := [(38,false),(45,false),(47,true),(54,true),(120,true)]
theorem der_31057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31057 :=
  CNF.rup_sound cl_31057 [cl_25162,cl_31041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25162 v h) (hints_cons _ _ _ (der_31041 v h) (by intro d hd; cases hd)))
def cl_31059 : CNF.NClause := [(59,false),(50,false),(42,false),(53,false),(121,true)]
theorem der_31059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31059 :=
  CNF.rup_sound cl_31059 [cl_25166,cl_30758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25166 v h) (hints_cons _ _ _ (der_30758 v h) (by intro d hd; cases hd)))
def cl_31060 : CNF.NClause := [(59,false),(50,false),(53,false),(39,true),(121,true)]
theorem der_31060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31060 :=
  CNF.rup_sound cl_31060 [cl_25168,cl_31059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25168 v h) (hints_cons _ _ _ (der_31059 v h) (by intro d hd; cases hd)))
def cl_31061 : CNF.NClause := [(59,false),(42,false),(53,false),(31,false),(121,true)]
theorem der_31061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31061 :=
  CNF.rup_sound cl_31061 [cl_25170,cl_25169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25170 v h) (hints_cons _ _ _ (der_25169 v h) (by intro d hd; cases hd)))
def cl_31062 : CNF.NClause := [(59,false),(39,false),(53,false),(31,false),(121,true)]
theorem der_31062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31062 :=
  CNF.rup_sound cl_31062 [cl_25171,cl_25169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25171 v h) (hints_cons _ _ _ (der_25169 v h) (by intro d hd; cases hd)))
def cl_31063 : CNF.NClause := [(59,false),(39,true),(53,false),(42,true),(121,true)]
theorem der_31063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31063 :=
  CNF.rup_sound cl_31063 [cl_25172,cl_31060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25172 v h) (hints_cons _ _ _ (der_31060 v h) (by intro d hd; cases hd)))
def cl_31064 : CNF.NClause := [(59,false),(50,false),(42,false),(39,false),(121,true)]
theorem der_31064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31064 :=
  CNF.rup_sound cl_31064 [cl_25173,cl_25165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25173 v h) (hints_cons _ _ _ (der_25165 v h) (by intro d hd; cases hd)))
def cl_31065 : CNF.NClause := [(59,false),(50,false),(42,false),(31,false),(121,true)]
theorem der_31065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31065 :=
  CNF.rup_sound cl_31065 [cl_25174,cl_31064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25174 v h) (hints_cons _ _ _ (der_31064 v h) (by intro d hd; cases hd)))
def cl_31066 : CNF.NClause := [(59,false),(50,false),(39,false),(31,false),(121,true)]
theorem der_31066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31066 :=
  CNF.rup_sound cl_31066 [cl_25175,cl_31064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25175 v h) (hints_cons _ _ _ (der_31064 v h) (by intro d hd; cases hd)))
def cl_31067 : CNF.NClause := [(59,false),(50,false),(31,false),(39,true),(121,true)]
theorem der_31067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31067 :=
  CNF.rup_sound cl_31067 [cl_25176,cl_31060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25176 v h) (hints_cons _ _ _ (der_31060 v h) (by intro d hd; cases hd)))
def cl_31069 : CNF.NClause := [(59,false),(42,false),(31,false),(53,true),(121,true)]
theorem der_31069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31069 :=
  CNF.rup_sound cl_31069 [cl_25178,cl_31065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25178 v h) (hints_cons _ _ _ (der_31065 v h) (by intro d hd; cases hd)))
def cl_31070 : CNF.NClause := [(59,false),(39,false),(31,false),(50,true),(121,true)]
theorem der_31070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31070 :=
  CNF.rup_sound cl_31070 [cl_25179,cl_31062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25179 v h) (hints_cons _ _ _ (der_31062 v h) (by intro d hd; cases hd)))
def cl_31072 : CNF.NClause := [(50,false),(42,false),(53,false),(31,false),(121,true)]
theorem der_31072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31072 :=
  CNF.rup_sound cl_31072 [cl_25182,cl_25181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25182 v h) (hints_cons _ _ _ (der_25181 v h) (by intro d hd; cases hd)))
def cl_31073 : CNF.NClause := [(50,false),(39,false),(53,false),(31,false),(121,true)]
theorem der_31073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31073 :=
  CNF.rup_sound cl_31073 [cl_25183,cl_31072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25183 v h) (hints_cons _ _ _ (der_31072 v h) (by intro d hd; cases hd)))
def cl_31074 : CNF.NClause := [(50,false),(31,false),(53,false),(59,true),(121,true)]
theorem der_31074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31074 :=
  CNF.rup_sound cl_31074 [cl_25184,cl_31073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25184 v h) (hints_cons _ _ _ (der_31073 v h) (by intro d hd; cases hd)))
def cl_31075 : CNF.NClause := [(42,false),(39,false),(53,false),(31,false),(121,true)]
theorem der_31075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31075 :=
  CNF.rup_sound cl_31075 [cl_25185,cl_31073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25185 v h) (hints_cons _ _ _ (der_31073 v h) (by intro d hd; cases hd)))
def cl_31076 : CNF.NClause := [(42,false),(31,false),(53,false),(59,true),(121,true)]
theorem der_31076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31076 :=
  CNF.rup_sound cl_31076 [cl_25186,cl_31075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25186 v h) (hints_cons _ _ _ (der_31075 v h) (by intro d hd; cases hd)))
def cl_31077 : CNF.NClause := [(39,false),(31,false),(53,false),(42,true),(121,true)]
theorem der_31077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31077 :=
  CNF.rup_sound cl_31077 [cl_25187,cl_31073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25187 v h) (hints_cons _ _ _ (der_31073 v h) (by intro d hd; cases hd)))
def cl_31078 : CNF.NClause := [(31,false),(42,true),(53,false),(59,true),(121,true)]
theorem der_31078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31078 :=
  CNF.rup_sound cl_31078 [cl_25188,cl_31074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25188 v h) (hints_cons _ _ _ (der_31074 v h) (by intro d hd; cases hd)))
def cl_31079 : CNF.NClause := [(50,false),(42,false),(39,false),(53,true),(121,true)]
theorem der_31079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31079 :=
  CNF.rup_sound cl_31079 [cl_25189,cl_31064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25189 v h) (hints_cons _ _ _ (der_31064 v h) (by intro d hd; cases hd)))
def cl_31080 : CNF.NClause := [(50,false),(42,false),(31,false),(39,true),(121,true)]
theorem der_31080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31080 :=
  CNF.rup_sound cl_31080 [cl_25190,cl_31065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25190 v h) (hints_cons _ _ _ (der_31065 v h) (by intro d hd; cases hd)))
def cl_31081 : CNF.NClause := [(50,false),(39,false),(31,false),(42,true),(121,true)]
theorem der_31081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31081 :=
  CNF.rup_sound cl_31081 [cl_25191,cl_31066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25191 v h) (hints_cons _ _ _ (der_31066 v h) (by intro d hd; cases hd)))
def cl_31082 : CNF.NClause := [(50,false),(31,false),(42,true),(59,true),(121,true)]
theorem der_31082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31082 :=
  CNF.rup_sound cl_31082 [cl_25192,cl_31074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25192 v h) (hints_cons _ _ _ (der_31074 v h) (by intro d hd; cases hd)))
def cl_31083 : CNF.NClause := [(42,false),(39,false),(31,false),(50,true),(121,true)]
theorem der_31083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31083 :=
  CNF.rup_sound cl_31083 [cl_25193,cl_31075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25193 v h) (hints_cons _ _ _ (der_31075 v h) (by intro d hd; cases hd)))
def cl_31084 : CNF.NClause := [(42,false),(31,false),(39,true),(53,true),(121,true)]
theorem der_31084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31084 :=
  CNF.rup_sound cl_31084 [cl_25194,cl_31069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25194 v h) (hints_cons _ _ _ (der_31069 v h) (by intro d hd; cases hd)))
def cl_31085 : CNF.NClause := [(39,false),(31,false),(42,true),(59,true),(121,true)]
theorem der_31085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31085 :=
  CNF.rup_sound cl_31085 [cl_25195,cl_31081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25195 v h) (hints_cons _ _ _ (der_31081 v h) (by intro d hd; cases hd)))
def cl_31086 : CNF.NClause := [(57,false),(55,false),(43,false),(49,true),(122,true)]
theorem der_31086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31086 :=
  CNF.rup_sound cl_31086 [cl_25200,cl_25199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25200 v h) (hints_cons _ _ _ (der_25199 v h) (by intro d hd; cases hd)))
def cl_31087 : CNF.NClause := [(57,false),(55,false),(49,true),(37,true),(122,true)]
theorem der_31087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31087 :=
  CNF.rup_sound cl_31087 [cl_25202,cl_31086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25202 v h) (hints_cons _ _ _ (der_31086 v h) (by intro d hd; cases hd)))
def cl_31088 : CNF.NClause := [(57,false),(49,false),(43,false),(31,false),(122,true)]
theorem der_31088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31088 :=
  CNF.rup_sound cl_31088 [cl_25204,cl_25196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25204 v h) (hints_cons _ _ _ (der_25196 v h) (by intro d hd; cases hd)))
def cl_31089 : CNF.NClause := [(57,false),(37,false),(49,false),(31,false),(122,true)]
theorem der_31089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31089 :=
  CNF.rup_sound cl_31089 [cl_25205,cl_31088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25205 v h) (hints_cons _ _ _ (der_31088 v h) (by intro d hd; cases hd)))
def cl_31090 : CNF.NClause := [(57,false),(49,false),(37,true),(43,true),(122,true)]
theorem der_31090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31090 :=
  CNF.rup_sound cl_31090 [cl_25206,cl_25198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25206 v h) (hints_cons _ _ _ (der_25198 v h) (by intro d hd; cases hd)))
def cl_31091 : CNF.NClause := [(57,false),(37,false),(43,false),(49,true),(122,true)]
theorem der_31091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31091 :=
  CNF.rup_sound cl_31091 [cl_25207,cl_25199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25207 v h) (hints_cons _ _ _ (der_25199 v h) (by intro d hd; cases hd)))
def cl_31092 : CNF.NClause := [(57,false),(49,true),(43,false),(37,true),(122,true)]
theorem der_31092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31092 :=
  CNF.rup_sound cl_31092 [cl_25208,cl_31086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25208 v h) (hints_cons _ _ _ (der_31086 v h) (by intro d hd; cases hd)))
def cl_31093 : CNF.NClause := [(57,false),(37,false),(49,true),(55,true),(122,true)]
theorem der_31093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31093 :=
  CNF.rup_sound cl_31093 [cl_25209,cl_31091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25209 v h) (hints_cons _ _ _ (der_31091 v h) (by intro d hd; cases hd)))
def cl_31094 : CNF.NClause := [(37,false),(55,false),(49,false),(31,false),(122,true)]
theorem der_31094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31094 :=
  CNF.rup_sound cl_31094 [cl_25213,cl_25211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25213 v h) (hints_cons _ _ _ (der_25211 v h) (by intro d hd; cases hd)))
def chunk016 : List CNF.NClause := [cl_30523,cl_30524,cl_30525,cl_30526,cl_30527,cl_30528,cl_30530,cl_30531,cl_30533,cl_30534,cl_30535,cl_30536,cl_30537,cl_30538,cl_30539,cl_30540,cl_30541,cl_30542,cl_30543,cl_30544,cl_30545,cl_30546,cl_30547,cl_30548,cl_30549,cl_30550,cl_30551,cl_30552,cl_30553,cl_30554,cl_30555,cl_30556,cl_30557,cl_30558,cl_30559,cl_30560,cl_30561,cl_30562,cl_30563,cl_30564,cl_30565,cl_30566,cl_30568,cl_30569,cl_30570,cl_30572,cl_30573,cl_30574,cl_30575,cl_30576,cl_30577,cl_30578,cl_30579,cl_30580,cl_30581,cl_30582,cl_30583,cl_30584,cl_30585,cl_30586,cl_30587,cl_30588,cl_30589,cl_30590,cl_30591,cl_30592,cl_30593,cl_30594,cl_30595,cl_30596,cl_30597,cl_30598,cl_30599,cl_30600,cl_30601,cl_30602,cl_30603,cl_30604,cl_30605,cl_30606,cl_30607,cl_30608,cl_30609,cl_30610,cl_30611,cl_30612,cl_30613,cl_30614,cl_30615,cl_30616,cl_30617,cl_30618,cl_30619,cl_30620,cl_30622,cl_30623,cl_30624,cl_30625,cl_30626,cl_30628,cl_30629,cl_30630,cl_30631,cl_30632,cl_30633,cl_30634,cl_30635,cl_30636,cl_30637,cl_30638,cl_30639,cl_30640,cl_30641,cl_30642,cl_30643,cl_30644,cl_30645,cl_30646,cl_30647,cl_30648,cl_30649,cl_30650,cl_30651,cl_30652,cl_30653,cl_30654,cl_30655,cl_30656,cl_30657,cl_30658,cl_30659,cl_30660,cl_30661,cl_30662,cl_30663,cl_30664,cl_30665,cl_30666,cl_30667,cl_30669,cl_30670,cl_30671,cl_30673,cl_30674,cl_30675,cl_30676,cl_30677,cl_30678,cl_30679,cl_30680,cl_30681,cl_30682,cl_30683,cl_30684,cl_30685,cl_30686,cl_30687,cl_30688,cl_30689,cl_30690,cl_30691,cl_30692,cl_30693,cl_30694,cl_30695,cl_30696,cl_30697,cl_30698,cl_30699,cl_30700,cl_30701,cl_30702,cl_30703,cl_30704,cl_30705,cl_30706,cl_30708,cl_30709,cl_30711,cl_30712,cl_30714,cl_30717,cl_30718,cl_30719,cl_30720,cl_30721,cl_30722,cl_30723,cl_30724,cl_30725,cl_30726,cl_30727,cl_30729,cl_30730,cl_30731,cl_30732,cl_30733,cl_30734,cl_30735,cl_30736,cl_30737,cl_30738,cl_30739,cl_30740,cl_30741,cl_30742,cl_30743,cl_30744,cl_30745,cl_30746,cl_30747,cl_30748,cl_30749,cl_30750,cl_30751,cl_30752,cl_30753,cl_30754,cl_30755,cl_30757,cl_30758,cl_30759,cl_30760,cl_30761,cl_30762,cl_30763,cl_30764,cl_30765,cl_30766,cl_30767,cl_30768,cl_30769,cl_30772,cl_30774,cl_30775,cl_30776,cl_30777,cl_30778,cl_30779,cl_30780,cl_30781,cl_30782,cl_30783,cl_30784,cl_30785,cl_30786,cl_30789,cl_30790,cl_30791,cl_30792,cl_30793,cl_30794,cl_30796,cl_30797,cl_30798,cl_30800,cl_30801,cl_30802,cl_30803,cl_30805,cl_30806,cl_30807,cl_30808,cl_30809,cl_30810,cl_30811,cl_30812,cl_30815,cl_30817,cl_30820,cl_30821,cl_30822,cl_30826,cl_30827,cl_30828,cl_30829,cl_30830,cl_30831,cl_30832,cl_30834,cl_30835,cl_30836,cl_30837,cl_30838,cl_30839,cl_30840,cl_30841,cl_30842,cl_30843,cl_30844,cl_30845,cl_30846,cl_30847,cl_30848,cl_30849,cl_30850,cl_30851,cl_30852,cl_30853,cl_30854,cl_30855,cl_30856,cl_30857,cl_30858,cl_30859,cl_30860,cl_30861,cl_30863,cl_30864,cl_30865,cl_30866,cl_30867,cl_30868,cl_30869,cl_30870,cl_30871,cl_30872,cl_30873,cl_30874,cl_30875,cl_30876,cl_30877,cl_30878,cl_30879,cl_30881,cl_30882,cl_30883,cl_30886,cl_30887,cl_30888,cl_30889,cl_30890,cl_30891,cl_30892,cl_30893,cl_30894,cl_30895,cl_30896,cl_30897,cl_30898,cl_30899,cl_30900,cl_30901,cl_30902,cl_30903,cl_30904,cl_30905,cl_30906,cl_30907,cl_30908,cl_30909,cl_30910,cl_30911,cl_30912,cl_30913,cl_30914,cl_30915,cl_30916,cl_30918,cl_30919,cl_30920,cl_30921,cl_30922,cl_30923,cl_30924,cl_30925,cl_30926,cl_30927,cl_30929,cl_30930,cl_30931,cl_30932,cl_30933,cl_30934,cl_30935,cl_30936,cl_30937,cl_30938,cl_30939,cl_30940,cl_30941,cl_30942,cl_30943,cl_30944,cl_30945,cl_30946,cl_30947,cl_30948,cl_30949,cl_30950,cl_30951,cl_30953,cl_30954,cl_30955,cl_30956,cl_30957,cl_30958,cl_30959,cl_30960,cl_30961,cl_30962,cl_30963,cl_30964,cl_30965,cl_30966,cl_30967,cl_30968,cl_30970,cl_30971,cl_30972,cl_30974,cl_30975,cl_30977,cl_30978,cl_30979,cl_30980,cl_30981,cl_30982,cl_30983,cl_30984,cl_30985,cl_30986,cl_30989,cl_30992,cl_30994,cl_30998,cl_30999,cl_31000,cl_31003,cl_31005,cl_31007,cl_31009,cl_31012,cl_31014,cl_31015,cl_31016,cl_31018,cl_31019,cl_31020,cl_31021,cl_31022,cl_31023,cl_31024,cl_31025,cl_31026,cl_31028,cl_31029,cl_31031,cl_31032,cl_31034,cl_31035,cl_31036,cl_31037,cl_31038,cl_31041,cl_31042,cl_31043,cl_31045,cl_31046,cl_31049,cl_31050,cl_31051,cl_31053,cl_31054,cl_31055,cl_31057,cl_31059,cl_31060,cl_31061,cl_31062,cl_31063,cl_31064,cl_31065,cl_31066,cl_31067,cl_31069,cl_31070,cl_31072,cl_31073,cl_31074,cl_31075,cl_31076,cl_31077,cl_31078,cl_31079,cl_31080,cl_31081,cl_31082,cl_31083,cl_31084,cl_31085,cl_31086,cl_31087,cl_31088,cl_31089,cl_31090,cl_31091,cl_31092,cl_31093,cl_31094]
theorem chunk_sound016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk016, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_30523 v h) (hints_cons _ _ _ (der_30524 v h) (hints_cons _ _ _ (der_30525 v h) (hints_cons _ _ _ (der_30526 v h) (hints_cons _ _ _ (der_30527 v h) (hints_cons _ _ _ (der_30528 v h) (hints_cons _ _ _ (der_30530 v h) (hints_cons _ _ _ (der_30531 v h) (hints_cons _ _ _ (der_30533 v h) (hints_cons _ _ _ (der_30534 v h) (hints_cons _ _ _ (der_30535 v h) (hints_cons _ _ _ (der_30536 v h) (hints_cons _ _ _ (der_30537 v h) (hints_cons _ _ _ (der_30538 v h) (hints_cons _ _ _ (der_30539 v h) (hints_cons _ _ _ (der_30540 v h) (hints_cons _ _ _ (der_30541 v h) (hints_cons _ _ _ (der_30542 v h) (hints_cons _ _ _ (der_30543 v h) (hints_cons _ _ _ (der_30544 v h) (hints_cons _ _ _ (der_30545 v h) (hints_cons _ _ _ (der_30546 v h) (hints_cons _ _ _ (der_30547 v h) (hints_cons _ _ _ (der_30548 v h) (hints_cons _ _ _ (der_30549 v h) (hints_cons _ _ _ (der_30550 v h) (hints_cons _ _ _ (der_30551 v h) (hints_cons _ _ _ (der_30552 v h) (hints_cons _ _ _ (der_30553 v h) (hints_cons _ _ _ (der_30554 v h) (hints_cons _ _ _ (der_30555 v h) (hints_cons _ _ _ (der_30556 v h) (hints_cons _ _ _ (der_30557 v h) (hints_cons _ _ _ (der_30558 v h) (hints_cons _ _ _ (der_30559 v h) (hints_cons _ _ _ (der_30560 v h) (hints_cons _ _ _ (der_30561 v h) (hints_cons _ _ _ (der_30562 v h) (hints_cons _ _ _ (der_30563 v h) (hints_cons _ _ _ (der_30564 v h) (hints_cons _ _ _ (der_30565 v h) (hints_cons _ _ _ (der_30566 v h) (hints_cons _ _ _ (der_30568 v h) (hints_cons _ _ _ (der_30569 v h) (hints_cons _ _ _ (der_30570 v h) (hints_cons _ _ _ (der_30572 v h) (hints_cons _ _ _ (der_30573 v h) (hints_cons _ _ _ (der_30574 v h) (hints_cons _ _ _ (der_30575 v h) (hints_cons _ _ _ (der_30576 v h) (hints_cons _ _ _ (der_30577 v h) (hints_cons _ _ _ (der_30578 v h) (hints_cons _ _ _ (der_30579 v h) (hints_cons _ _ _ (der_30580 v h) (hints_cons _ _ _ (der_30581 v h) (hints_cons _ _ _ (der_30582 v h) (hints_cons _ _ _ (der_30583 v h) (hints_cons _ _ _ (der_30584 v h) (hints_cons _ _ _ (der_30585 v h) (hints_cons _ _ _ (der_30586 v h) (hints_cons _ _ _ (der_30587 v h) (hints_cons _ _ _ (der_30588 v h) (hints_cons _ _ _ (der_30589 v h) (hints_cons _ _ _ (der_30590 v h) (hints_cons _ _ _ (der_30591 v h) (hints_cons _ _ _ (der_30592 v h) (hints_cons _ _ _ (der_30593 v h) (hints_cons _ _ _ (der_30594 v h) (hints_cons _ _ _ (der_30595 v h) (hints_cons _ _ _ (der_30596 v h) (hints_cons _ _ _ (der_30597 v h) (hints_cons _ _ _ (der_30598 v h) (hints_cons _ _ _ (der_30599 v h) (hints_cons _ _ _ (der_30600 v h) (hints_cons _ _ _ (der_30601 v h) (hints_cons _ _ _ (der_30602 v h) (hints_cons _ _ _ (der_30603 v h) (hints_cons _ _ _ (der_30604 v h) (hints_cons _ _ _ (der_30605 v h) (hints_cons _ _ _ (der_30606 v h) (hints_cons _ _ _ (der_30607 v h) (hints_cons _ _ _ (der_30608 v h) (hints_cons _ _ _ (der_30609 v h) (hints_cons _ _ _ (der_30610 v h) (hints_cons _ _ _ (der_30611 v h) (hints_cons _ _ _ (der_30612 v h) (hints_cons _ _ _ (der_30613 v h) (hints_cons _ _ _ (der_30614 v h) (hints_cons _ _ _ (der_30615 v h) (hints_cons _ _ _ (der_30616 v h) (hints_cons _ _ _ (der_30617 v h) (hints_cons _ _ _ (der_30618 v h) (hints_cons _ _ _ (der_30619 v h) (hints_cons _ _ _ (der_30620 v h) (hints_cons _ _ _ (der_30622 v h) (hints_cons _ _ _ (der_30623 v h) (hints_cons _ _ _ (der_30624 v h) (hints_cons _ _ _ (der_30625 v h) (hints_cons _ _ _ (der_30626 v h) (hints_cons _ _ _ (der_30628 v h) (hints_cons _ _ _ (der_30629 v h) (hints_cons _ _ _ (der_30630 v h) (hints_cons _ _ _ (der_30631 v h) (hints_cons _ _ _ (der_30632 v h) (hints_cons _ _ _ (der_30633 v h) (hints_cons _ _ _ (der_30634 v h) (hints_cons _ _ _ (der_30635 v h) (hints_cons _ _ _ (der_30636 v h) (hints_cons _ _ _ (der_30637 v h) (hints_cons _ _ _ (der_30638 v h) (hints_cons _ _ _ (der_30639 v h) (hints_cons _ _ _ (der_30640 v h) (hints_cons _ _ _ (der_30641 v h) (hints_cons _ _ _ (der_30642 v h) (hints_cons _ _ _ (der_30643 v h) (hints_cons _ _ _ (der_30644 v h) (hints_cons _ _ _ (der_30645 v h) (hints_cons _ _ _ (der_30646 v h) (hints_cons _ _ _ (der_30647 v h) (hints_cons _ _ _ (der_30648 v h) (hints_cons _ _ _ (der_30649 v h) (hints_cons _ _ _ (der_30650 v h) (hints_cons _ _ _ (der_30651 v h) (hints_cons _ _ _ (der_30652 v h) (hints_cons _ _ _ (der_30653 v h) (hints_cons _ _ _ (der_30654 v h) (hints_cons _ _ _ (der_30655 v h) (hints_cons _ _ _ (der_30656 v h) (hints_cons _ _ _ (der_30657 v h) (hints_cons _ _ _ (der_30658 v h) (hints_cons _ _ _ (der_30659 v h) (hints_cons _ _ _ (der_30660 v h) (hints_cons _ _ _ (der_30661 v h) (hints_cons _ _ _ (der_30662 v h) (hints_cons _ _ _ (der_30663 v h) (hints_cons _ _ _ (der_30664 v h) (hints_cons _ _ _ (der_30665 v h) (hints_cons _ _ _ (der_30666 v h) (hints_cons _ _ _ (der_30667 v h) (hints_cons _ _ _ (der_30669 v h) (hints_cons _ _ _ (der_30670 v h) (hints_cons _ _ _ (der_30671 v h) (hints_cons _ _ _ (der_30673 v h) (hints_cons _ _ _ (der_30674 v h) (hints_cons _ _ _ (der_30675 v h) (hints_cons _ _ _ (der_30676 v h) (hints_cons _ _ _ (der_30677 v h) (hints_cons _ _ _ (der_30678 v h) (hints_cons _ _ _ (der_30679 v h) (hints_cons _ _ _ (der_30680 v h) (hints_cons _ _ _ (der_30681 v h) (hints_cons _ _ _ (der_30682 v h) (hints_cons _ _ _ (der_30683 v h) (hints_cons _ _ _ (der_30684 v h) (hints_cons _ _ _ (der_30685 v h) (hints_cons _ _ _ (der_30686 v h) (hints_cons _ _ _ (der_30687 v h) (hints_cons _ _ _ (der_30688 v h) (hints_cons _ _ _ (der_30689 v h) (hints_cons _ _ _ (der_30690 v h) (hints_cons _ _ _ (der_30691 v h) (hints_cons _ _ _ (der_30692 v h) (hints_cons _ _ _ (der_30693 v h) (hints_cons _ _ _ (der_30694 v h) (hints_cons _ _ _ (der_30695 v h) (hints_cons _ _ _ (der_30696 v h) (hints_cons _ _ _ (der_30697 v h) (hints_cons _ _ _ (der_30698 v h) (hints_cons _ _ _ (der_30699 v h) (hints_cons _ _ _ (der_30700 v h) (hints_cons _ _ _ (der_30701 v h) (hints_cons _ _ _ (der_30702 v h) (hints_cons _ _ _ (der_30703 v h) (hints_cons _ _ _ (der_30704 v h) (hints_cons _ _ _ (der_30705 v h) (hints_cons _ _ _ (der_30706 v h) (hints_cons _ _ _ (der_30708 v h) (hints_cons _ _ _ (der_30709 v h) (hints_cons _ _ _ (der_30711 v h) (hints_cons _ _ _ (der_30712 v h) (hints_cons _ _ _ (der_30714 v h) (hints_cons _ _ _ (der_30717 v h) (hints_cons _ _ _ (der_30718 v h) (hints_cons _ _ _ (der_30719 v h) (hints_cons _ _ _ (der_30720 v h) (hints_cons _ _ _ (der_30721 v h) (hints_cons _ _ _ (der_30722 v h) (hints_cons _ _ _ (der_30723 v h) (hints_cons _ _ _ (der_30724 v h) (hints_cons _ _ _ (der_30725 v h) (hints_cons _ _ _ (der_30726 v h) (hints_cons _ _ _ (der_30727 v h) (hints_cons _ _ _ (der_30729 v h) (hints_cons _ _ _ (der_30730 v h) (hints_cons _ _ _ (der_30731 v h) (hints_cons _ _ _ (der_30732 v h) (hints_cons _ _ _ (der_30733 v h) (hints_cons _ _ _ (der_30734 v h) (hints_cons _ _ _ (der_30735 v h) (hints_cons _ _ _ (der_30736 v h) (hints_cons _ _ _ (der_30737 v h) (hints_cons _ _ _ (der_30738 v h) (hints_cons _ _ _ (der_30739 v h) (hints_cons _ _ _ (der_30740 v h) (hints_cons _ _ _ (der_30741 v h) (hints_cons _ _ _ (der_30742 v h) (hints_cons _ _ _ (der_30743 v h) (hints_cons _ _ _ (der_30744 v h) (hints_cons _ _ _ (der_30745 v h) (hints_cons _ _ _ (der_30746 v h) (hints_cons _ _ _ (der_30747 v h) (hints_cons _ _ _ (der_30748 v h) (hints_cons _ _ _ (der_30749 v h) (hints_cons _ _ _ (der_30750 v h) (hints_cons _ _ _ (der_30751 v h) (hints_cons _ _ _ (der_30752 v h) (hints_cons _ _ _ (der_30753 v h) (hints_cons _ _ _ (der_30754 v h) (hints_cons _ _ _ (der_30755 v h) (hints_cons _ _ _ (der_30757 v h) (hints_cons _ _ _ (der_30758 v h) (hints_cons _ _ _ (der_30759 v h) (hints_cons _ _ _ (der_30760 v h) (hints_cons _ _ _ (der_30761 v h) (hints_cons _ _ _ (der_30762 v h) (hints_cons _ _ _ (der_30763 v h) (hints_cons _ _ _ (der_30764 v h) (hints_cons _ _ _ (der_30765 v h) (hints_cons _ _ _ (der_30766 v h) (hints_cons _ _ _ (der_30767 v h) (hints_cons _ _ _ (der_30768 v h) (hints_cons _ _ _ (der_30769 v h) (hints_cons _ _ _ (der_30772 v h) (hints_cons _ _ _ (der_30774 v h) (hints_cons _ _ _ (der_30775 v h) (hints_cons _ _ _ (der_30776 v h) (hints_cons _ _ _ (der_30777 v h) (hints_cons _ _ _ (der_30778 v h) (hints_cons _ _ _ (der_30779 v h) (hints_cons _ _ _ (der_30780 v h) (hints_cons _ _ _ (der_30781 v h) (hints_cons _ _ _ (der_30782 v h) (hints_cons _ _ _ (der_30783 v h) (hints_cons _ _ _ (der_30784 v h) (hints_cons _ _ _ (der_30785 v h) (hints_cons _ _ _ (der_30786 v h) (hints_cons _ _ _ (der_30789 v h) (hints_cons _ _ _ (der_30790 v h) (hints_cons _ _ _ (der_30791 v h) (hints_cons _ _ _ (der_30792 v h) (hints_cons _ _ _ (der_30793 v h) (hints_cons _ _ _ (der_30794 v h) (hints_cons _ _ _ (der_30796 v h) (hints_cons _ _ _ (der_30797 v h) (hints_cons _ _ _ (der_30798 v h) (hints_cons _ _ _ (der_30800 v h) (hints_cons _ _ _ (der_30801 v h) (hints_cons _ _ _ (der_30802 v h) (hints_cons _ _ _ (der_30803 v h) (hints_cons _ _ _ (der_30805 v h) (hints_cons _ _ _ (der_30806 v h) (hints_cons _ _ _ (der_30807 v h) (hints_cons _ _ _ (der_30808 v h) (hints_cons _ _ _ (der_30809 v h) (hints_cons _ _ _ (der_30810 v h) (hints_cons _ _ _ (der_30811 v h) (hints_cons _ _ _ (der_30812 v h) (hints_cons _ _ _ (der_30815 v h) (hints_cons _ _ _ (der_30817 v h) (hints_cons _ _ _ (der_30820 v h) (hints_cons _ _ _ (der_30821 v h) (hints_cons _ _ _ (der_30822 v h) (hints_cons _ _ _ (der_30826 v h) (hints_cons _ _ _ (der_30827 v h) (hints_cons _ _ _ (der_30828 v h) (hints_cons _ _ _ (der_30829 v h) (hints_cons _ _ _ (der_30830 v h) (hints_cons _ _ _ (der_30831 v h) (hints_cons _ _ _ (der_30832 v h) (hints_cons _ _ _ (der_30834 v h) (hints_cons _ _ _ (der_30835 v h) (hints_cons _ _ _ (der_30836 v h) (hints_cons _ _ _ (der_30837 v h) (hints_cons _ _ _ (der_30838 v h) (hints_cons _ _ _ (der_30839 v h) (hints_cons _ _ _ (der_30840 v h) (hints_cons _ _ _ (der_30841 v h) (hints_cons _ _ _ (der_30842 v h) (hints_cons _ _ _ (der_30843 v h) (hints_cons _ _ _ (der_30844 v h) (hints_cons _ _ _ (der_30845 v h) (hints_cons _ _ _ (der_30846 v h) (hints_cons _ _ _ (der_30847 v h) (hints_cons _ _ _ (der_30848 v h) (hints_cons _ _ _ (der_30849 v h) (hints_cons _ _ _ (der_30850 v h) (hints_cons _ _ _ (der_30851 v h) (hints_cons _ _ _ (der_30852 v h) (hints_cons _ _ _ (der_30853 v h) (hints_cons _ _ _ (der_30854 v h) (hints_cons _ _ _ (der_30855 v h) (hints_cons _ _ _ (der_30856 v h) (hints_cons _ _ _ (der_30857 v h) (hints_cons _ _ _ (der_30858 v h) (hints_cons _ _ _ (der_30859 v h) (hints_cons _ _ _ (der_30860 v h) (hints_cons _ _ _ (der_30861 v h) (hints_cons _ _ _ (der_30863 v h) (hints_cons _ _ _ (der_30864 v h) (hints_cons _ _ _ (der_30865 v h) (hints_cons _ _ _ (der_30866 v h) (hints_cons _ _ _ (der_30867 v h) (hints_cons _ _ _ (der_30868 v h) (hints_cons _ _ _ (der_30869 v h) (hints_cons _ _ _ (der_30870 v h) (hints_cons _ _ _ (der_30871 v h) (hints_cons _ _ _ (der_30872 v h) (hints_cons _ _ _ (der_30873 v h) (hints_cons _ _ _ (der_30874 v h) (hints_cons _ _ _ (der_30875 v h) (hints_cons _ _ _ (der_30876 v h) (hints_cons _ _ _ (der_30877 v h) (hints_cons _ _ _ (der_30878 v h) (hints_cons _ _ _ (der_30879 v h) (hints_cons _ _ _ (der_30881 v h) (hints_cons _ _ _ (der_30882 v h) (hints_cons _ _ _ (der_30883 v h) (hints_cons _ _ _ (der_30886 v h) (hints_cons _ _ _ (der_30887 v h) (hints_cons _ _ _ (der_30888 v h) (hints_cons _ _ _ (der_30889 v h) (hints_cons _ _ _ (der_30890 v h) (hints_cons _ _ _ (der_30891 v h) (hints_cons _ _ _ (der_30892 v h) (hints_cons _ _ _ (der_30893 v h) (hints_cons _ _ _ (der_30894 v h) (hints_cons _ _ _ (der_30895 v h) (hints_cons _ _ _ (der_30896 v h) (hints_cons _ _ _ (der_30897 v h) (hints_cons _ _ _ (der_30898 v h) (hints_cons _ _ _ (der_30899 v h) (hints_cons _ _ _ (der_30900 v h) (hints_cons _ _ _ (der_30901 v h) (hints_cons _ _ _ (der_30902 v h) (hints_cons _ _ _ (der_30903 v h) (hints_cons _ _ _ (der_30904 v h) (hints_cons _ _ _ (der_30905 v h) (hints_cons _ _ _ (der_30906 v h) (hints_cons _ _ _ (der_30907 v h) (hints_cons _ _ _ (der_30908 v h) (hints_cons _ _ _ (der_30909 v h) (hints_cons _ _ _ (der_30910 v h) (hints_cons _ _ _ (der_30911 v h) (hints_cons _ _ _ (der_30912 v h) (hints_cons _ _ _ (der_30913 v h) (hints_cons _ _ _ (der_30914 v h) (hints_cons _ _ _ (der_30915 v h) (hints_cons _ _ _ (der_30916 v h) (hints_cons _ _ _ (der_30918 v h) (hints_cons _ _ _ (der_30919 v h) (hints_cons _ _ _ (der_30920 v h) (hints_cons _ _ _ (der_30921 v h) (hints_cons _ _ _ (der_30922 v h) (hints_cons _ _ _ (der_30923 v h) (hints_cons _ _ _ (der_30924 v h) (hints_cons _ _ _ (der_30925 v h) (hints_cons _ _ _ (der_30926 v h) (hints_cons _ _ _ (der_30927 v h) (hints_cons _ _ _ (der_30929 v h) (hints_cons _ _ _ (der_30930 v h) (hints_cons _ _ _ (der_30931 v h) (hints_cons _ _ _ (der_30932 v h) (hints_cons _ _ _ (der_30933 v h) (hints_cons _ _ _ (der_30934 v h) (hints_cons _ _ _ (der_30935 v h) (hints_cons _ _ _ (der_30936 v h) (hints_cons _ _ _ (der_30937 v h) (hints_cons _ _ _ (der_30938 v h) (hints_cons _ _ _ (der_30939 v h) (hints_cons _ _ _ (der_30940 v h) (hints_cons _ _ _ (der_30941 v h) (hints_cons _ _ _ (der_30942 v h) (hints_cons _ _ _ (der_30943 v h) (hints_cons _ _ _ (der_30944 v h) (hints_cons _ _ _ (der_30945 v h) (hints_cons _ _ _ (der_30946 v h) (hints_cons _ _ _ (der_30947 v h) (hints_cons _ _ _ (der_30948 v h) (hints_cons _ _ _ (der_30949 v h) (hints_cons _ _ _ (der_30950 v h) (hints_cons _ _ _ (der_30951 v h) (hints_cons _ _ _ (der_30953 v h) (hints_cons _ _ _ (der_30954 v h) (hints_cons _ _ _ (der_30955 v h) (hints_cons _ _ _ (der_30956 v h) (hints_cons _ _ _ (der_30957 v h) (hints_cons _ _ _ (der_30958 v h) (hints_cons _ _ _ (der_30959 v h) (hints_cons _ _ _ (der_30960 v h) (hints_cons _ _ _ (der_30961 v h) (hints_cons _ _ _ (der_30962 v h) (hints_cons _ _ _ (der_30963 v h) (hints_cons _ _ _ (der_30964 v h) (hints_cons _ _ _ (der_30965 v h) (hints_cons _ _ _ (der_30966 v h) (hints_cons _ _ _ (der_30967 v h) (hints_cons _ _ _ (der_30968 v h) (hints_cons _ _ _ (der_30970 v h) (hints_cons _ _ _ (der_30971 v h) (hints_cons _ _ _ (der_30972 v h) (hints_cons _ _ _ (der_30974 v h) (hints_cons _ _ _ (der_30975 v h) (hints_cons _ _ _ (der_30977 v h) (hints_cons _ _ _ (der_30978 v h) (hints_cons _ _ _ (der_30979 v h) (hints_cons _ _ _ (der_30980 v h) (hints_cons _ _ _ (der_30981 v h) (hints_cons _ _ _ (der_30982 v h) (hints_cons _ _ _ (der_30983 v h) (hints_cons _ _ _ (der_30984 v h) (hints_cons _ _ _ (der_30985 v h) (hints_cons _ _ _ (der_30986 v h) (hints_cons _ _ _ (der_30989 v h) (hints_cons _ _ _ (der_30992 v h) (hints_cons _ _ _ (der_30994 v h) (hints_cons _ _ _ (der_30998 v h) (hints_cons _ _ _ (der_30999 v h) (hints_cons _ _ _ (der_31000 v h) (hints_cons _ _ _ (der_31003 v h) (hints_cons _ _ _ (der_31005 v h) (hints_cons _ _ _ (der_31007 v h) (hints_cons _ _ _ (der_31009 v h) (hints_cons _ _ _ (der_31012 v h) (hints_cons _ _ _ (der_31014 v h) (hints_cons _ _ _ (der_31015 v h) (hints_cons _ _ _ (der_31016 v h) (hints_cons _ _ _ (der_31018 v h) (hints_cons _ _ _ (der_31019 v h) (hints_cons _ _ _ (der_31020 v h) (hints_cons _ _ _ (der_31021 v h) (hints_cons _ _ _ (der_31022 v h) (hints_cons _ _ _ (der_31023 v h) (hints_cons _ _ _ (der_31024 v h) (hints_cons _ _ _ (der_31025 v h) (hints_cons _ _ _ (der_31026 v h) (hints_cons _ _ _ (der_31028 v h) (hints_cons _ _ _ (der_31029 v h) (hints_cons _ _ _ (der_31031 v h) (hints_cons _ _ _ (der_31032 v h) (hints_cons _ _ _ (der_31034 v h) (hints_cons _ _ _ (der_31035 v h) (hints_cons _ _ _ (der_31036 v h) (hints_cons _ _ _ (der_31037 v h) (hints_cons _ _ _ (der_31038 v h) (hints_cons _ _ _ (der_31041 v h) (hints_cons _ _ _ (der_31042 v h) (hints_cons _ _ _ (der_31043 v h) (hints_cons _ _ _ (der_31045 v h) (hints_cons _ _ _ (der_31046 v h) (hints_cons _ _ _ (der_31049 v h) (hints_cons _ _ _ (der_31050 v h) (hints_cons _ _ _ (der_31051 v h) (hints_cons _ _ _ (der_31053 v h) (hints_cons _ _ _ (der_31054 v h) (hints_cons _ _ _ (der_31055 v h) (hints_cons _ _ _ (der_31057 v h) (hints_cons _ _ _ (der_31059 v h) (hints_cons _ _ _ (der_31060 v h) (hints_cons _ _ _ (der_31061 v h) (hints_cons _ _ _ (der_31062 v h) (hints_cons _ _ _ (der_31063 v h) (hints_cons _ _ _ (der_31064 v h) (hints_cons _ _ _ (der_31065 v h) (hints_cons _ _ _ (der_31066 v h) (hints_cons _ _ _ (der_31067 v h) (hints_cons _ _ _ (der_31069 v h) (hints_cons _ _ _ (der_31070 v h) (hints_cons _ _ _ (der_31072 v h) (hints_cons _ _ _ (der_31073 v h) (hints_cons _ _ _ (der_31074 v h) (hints_cons _ _ _ (der_31075 v h) (hints_cons _ _ _ (der_31076 v h) (hints_cons _ _ _ (der_31077 v h) (hints_cons _ _ _ (der_31078 v h) (hints_cons _ _ _ (der_31079 v h) (hints_cons _ _ _ (der_31080 v h) (hints_cons _ _ _ (der_31081 v h) (hints_cons _ _ _ (der_31082 v h) (hints_cons _ _ _ (der_31083 v h) (hints_cons _ _ _ (der_31084 v h) (hints_cons _ _ _ (der_31085 v h) (hints_cons _ _ _ (der_31086 v h) (hints_cons _ _ _ (der_31087 v h) (hints_cons _ _ _ (der_31088 v h) (hints_cons _ _ _ (der_31089 v h) (hints_cons _ _ _ (der_31090 v h) (hints_cons _ _ _ (der_31091 v h) (hints_cons _ _ _ (der_31092 v h) (hints_cons _ _ _ (der_31093 v h) (hints_cons _ _ _ (der_31094 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix016 := prefix015 ++ chunk016
theorem prefix_sound016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix016, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound015 v h c hc
  · exact chunk_sound016 v h c hc
end Percolation.NReplay
